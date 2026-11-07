#!/usr/bin/env bash
# Check the layout rules for rust/Libsignal/Proofs/ and rust/Libsignal/Specs/ in
# CODING_GUIDELINES.md ("Lean specifications").
#
# 1. No directory under Proofs/ or Specs/ is named after a tool: Aeneas or Charon, in any case.
# 2. Standard-library files live under Proofs/Std/ and Specs/Std/. A .lean file outside these
#    fails if it opens a namespace rooted at `core`, `alloc` or `std`, or at `Aeneas.Std` (where
#    the extraction backend puts std items), or declares or recalls a name with one of those roots.
# 3. Every proof file with a public theorem or definition has a summary: the Specs/ file at the
#    nearest ancestor of its path (Proofs/Core/Address/Kind.lean has Specs/Core/Address.lean).
#    The summary recalls each public `theorem` or `lemma` of the proof file and prints the axioms
#    of each public `def`, `abbrev` or `structure`.
# 4. In a summary, every recalled theorem also has an axiom check, and every `#print axioms`
#    command sits directly under `#guard_msgs`.
#
# Rules 3 and 4 read the files with comments removed: nested `/- ... -/` blocks (doc comments
# included) and `--` line comments. A recall or a guard inside a comment does not count.
#
# What the script cannot see:
# - Rule 2 is a namespace test. It misses a std item that the extraction places in a libsignal
#   namespace, such as `libsignal_protocol.Box.Insts.CoreConvertAsRef` (in Proofs/Std/Alloc/Boxed/).
# - That a summary path mirrors the Rust source file. Rule 3 checks only that a summary sits at an
#   ancestor of the proof path.
# - A declaration whose keyword is not at the start of its line.
# - Two declarations with the same last name component. Rule 3 compares only that component, so a
#   recall of either declaration satisfies it.
# - That a recalled statement matches the theorem, or that a guard lists the right axioms. The Lean
#   build checks both.
# - Axiom checks of extracted definitions, such as the entry points in Specs/Protocol/Pqxdh.lean,
#   which no proof file declares.
# - Comment markers inside character literals. The comment filter skips string literals only.
#
# Run from the repository root:
#   scripts/spec-layout-check.sh [ROOT]   checks ROOT/rust/Libsignal (ROOT defaults to .)
#   scripts/spec-layout-check.sh --self-test
#                                         checks that a good tree passes and that each tree with
#                                         one planted violation fails with the expected message
set -euo pipefail

# Print a Lean file with its comments replaced by nothing, keeping one output line per input line.
strip_comments() {
  awk '
    {
      line = $0; out = ""; n = length(line); i = 1; instr = 0
      while (i <= n) {
        two = substr(line, i, 2); ch = substr(line, i, 1)
        if (depth > 0) {
          if (two == "/-") { depth++; i += 2; continue }
          if (two == "-/") { depth--; i += 2; continue }
          i++; continue
        }
        if (instr) {
          out = out ch
          if (ch == "\\") { out = out substr(line, i + 1, 1); i += 2; continue }
          if (ch == "\"") instr = 0
          i++; continue
        }
        if (two == "/-") { depth = 1; i += 2; continue }
        if (two == "--") break
        if (ch == "\"") instr = 1
        out = out ch; i++
      }
      print out
    }' "$1"
}

check() {
  local root=$1
  local lib=$root/rust/Libsignal
  local proofs=$lib/Proofs specs=$lib/Specs
  local status=0
  local work
  work=$(mktemp -d)

  local tool_dirs
  tool_dirs=$(find "$proofs" "$specs" -type d \( -iname aeneas -o -iname charon \))
  if [ -n "$tool_dirs" ]; then
    echo "Directories named after a tool:"
    echo "$tool_dirs"
    status=1
  fi

  local std_root='(Aeneas\.Std|core|alloc|std)(\.|[[:space:]]|$)'
  local keywords='namespace|theorem|lemma|def|abbrev|structure|instance|recall'
  local misplaced
  misplaced=$(find "$proofs" "$specs" -name '*.lean' -not -path "$proofs/Std/*" \
      -not -path "$specs/Std/*" -print0 \
    | xargs -0 grep -HnE "^[[:space:]]*($keywords)[[:space:]]+$std_root" \
    || true)
  if [ -n "$misplaced" ]; then
    echo "Standard-library items outside Proofs/Std/ and Specs/Std/:"
    echo "$misplaced"
    status=1
  fi

  local file rel dir summary name active
  while IFS= read -r -d '' file; do
    rel=${file#"$proofs"/}
    active=$work/proof.lean
    strip_comments "$file" > "$active"
    local theorems defs
    theorems=$(grep -E '^(theorem|lemma)[[:space:]]' "$active" | awk '{print $2}' || true)
    defs=$(grep -E '^(noncomputable[[:space:]]+)?(def|abbrev|structure)[[:space:]]' "$active" \
      | sed -E 's/^(noncomputable[[:space:]]+)?(def|abbrev|structure)[[:space:]]+//' \
      | awk '{print $1}' || true)
    [ -z "$theorems$defs" ] && continue
    summary=
    dir=$(dirname "$rel")
    while [ "$dir" != . ]; do
      if [ -f "$specs/$dir.lean" ]; then summary=$specs/$dir.lean; break; fi
      dir=$(dirname "$dir")
    done
    if [ -z "$summary" ]; then
      echo "No summary at an ancestor of Proofs/$rel"
      status=1
      continue
    fi
    strip_comments "$summary" > "$work/summary.lean"
    for name in $theorems; do
      if ! grep -qE "^recall[[:space:]]+([^[:space:]]*\.)?${name##*.}([[:space:]]|$)" \
          "$work/summary.lean"; then
        echo "Theorem $name of Proofs/$rel is not recalled in ${summary#"$lib"/}"
        status=1
      fi
    done
    for name in $defs; do
      if ! grep -qE "^#print axioms[[:space:]]+([^[:space:]]*\.)?${name##*.}[[:space:]]*$" \
          "$work/summary.lean"; then
        echo "Definition $name of Proofs/$rel has no axiom check in ${summary#"$lib"/}"
        status=1
      fi
    done
  done < <(find "$proofs" -name '*.lean' -print0)

  while IFS= read -r -d '' file; do
    active=$work/spec.lean
    strip_comments "$file" > "$active"
    for name in $(grep -E '^recall[[:space:]]' "$active" | awk '{print $2}' || true); do
      if ! grep -qE "^#print axioms[[:space:]]+${name//./\\.}[[:space:]]*$" "$active"; then
        echo "Recalled $name has no axiom check in ${file#"$lib"/}"
        status=1
      fi
    done
    local unguarded
    unguarded=$(awk -v f="${file#"$lib"/}" '/^#print axioms/ && prev !~ /^#guard_msgs/ {
        print f ":" FNR ": " $0 } { prev = $0 }' "$active")
    if [ -n "$unguarded" ]; then
      echo "Axiom checks without #guard_msgs:"
      echo "$unguarded"
      status=1
    fi
  done < <(find "$specs" -name '*.lean' -print0)

  rm -rf "$work"
  return "$status"
}

self_test() {
  local tmp failed=0
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' RETURN

  # A good tree: one proof file with a theorem and a definition, and its summary.
  make_good() {
    local r=$1
    mkdir -p "$r/rust/Libsignal/Proofs/Core/Address" "$r/rust/Libsignal/Specs/Core"
    printf '%s\n' 'namespace libsignal_core.address.ServiceId' \
      'def helper : Nat := 0' '@[step]' 'theorem kind_spec : True := trivial' \
      'private theorem aux : True := trivial' 'end libsignal_core.address.ServiceId' \
      > "$r/rust/Libsignal/Proofs/Core/Address/Kind.lean"
    printf '%s\n' 'recall libsignal_core.address.ServiceId.kind_spec : True' \
      '/-- info: ... -/' '#guard_msgs in' \
      '#print axioms libsignal_core.address.ServiceId.kind_spec' \
      '#guard_msgs in' '#print axioms libsignal_core.address.ServiceId.helper' \
      > "$r/rust/Libsignal/Specs/Core/Address.lean"
  }

  # expect pass LABEL TREE, or expect fail LABEL TREE MESSAGE: a failing tree must print MESSAGE.
  expect() {
    local want=$1 label=$2 r=$3 message=${4:-}
    if check "$r" > "$tmp/out" 2>&1; then got=pass; else got=fail; fi
    if [ "$got" != "$want" ]; then
      echo "SELF-TEST FAILED: $label: expected $want, got $got"
      cat "$tmp/out"
      failed=1
    elif [ -n "$message" ] && ! grep -qF -- "$message" "$tmp/out"; then
      echo "SELF-TEST FAILED: $label: output lacks \"$message\""
      cat "$tmp/out"
      failed=1
    fi
  }

  local spec=rust/Libsignal/Specs/Core/Address.lean
  local proof=rust/Libsignal/Proofs/Core/Address/Kind.lean

  make_good "$tmp/good"
  expect pass "good tree" "$tmp/good"

  make_good "$tmp/r1"
  mkdir -p "$tmp/r1/rust/Libsignal/Proofs/Aeneas"
  expect fail "rule 1, tool-named directory" "$tmp/r1" "Directories named after a tool"

  make_good "$tmp/r2"
  printf '%s\n' 'recall Aeneas.Std.alloc.vec.Vec.foo : True' '#guard_msgs in' \
    '#print axioms Aeneas.Std.alloc.vec.Vec.foo' >> "$tmp/r2/$spec"
  expect fail "rule 2, std item outside Std/" "$tmp/r2" "Standard-library items outside"

  make_good "$tmp/r3a"
  rm "$tmp/r3a/$spec"
  expect fail "rule 3, no summary" "$tmp/r3a" "No summary at an ancestor"

  make_good "$tmp/r3b"
  echo 'theorem raw_uuid_spec : True := trivial' >> "$tmp/r3b/$proof"
  expect fail "rule 3, theorem not recalled" "$tmp/r3b" "Theorem raw_uuid_spec"

  make_good "$tmp/r3c"
  echo 'abbrev Bytes : Type := Nat' >> "$tmp/r3c/$proof"
  expect fail "rule 3, definition without axiom check" "$tmp/r3c" "Definition Bytes"

  make_good "$tmp/r3d"
  printf '%s\n' '/-' 'recall libsignal_core.address.ServiceId.kind_spec : True' \
    '#guard_msgs in' '#print axioms libsignal_core.address.ServiceId.kind_spec' '-/' \
    '#guard_msgs in' '#print axioms libsignal_core.address.ServiceId.helper' > "$tmp/r3d/$spec"
  expect fail "rule 3, recall inside a block comment" "$tmp/r3d" "Theorem kind_spec"

  make_good "$tmp/r4a"
  echo 'recall libsignal_core.address.ServiceId.other : True' >> "$tmp/r4a/$spec"
  expect fail "rule 4, recall without axiom check" "$tmp/r4a" "Recalled"

  make_good "$tmp/r4b"
  echo '#print axioms libsignal_core.address.ServiceId.kind' >> "$tmp/r4b/$spec"
  expect fail "rule 4, axiom check without #guard_msgs" "$tmp/r4b" "without #guard_msgs"

  make_good "$tmp/r4c"
  printf '%s\n' 'recall libsignal_core.address.ServiceId.kind_spec : True' '/-' \
    '#guard_msgs in' '#print axioms libsignal_core.address.ServiceId.kind_spec' '-/' \
    '#guard_msgs in' '#print axioms libsignal_core.address.ServiceId.helper' > "$tmp/r4c/$spec"
  expect fail "rule 4, axiom check inside a block comment" "$tmp/r4c" "Recalled"

  make_good "$tmp/r4d"
  printf '%s\n' 'recall libsignal_core.address.ServiceId.kind_spec : True' \
    '#guard_msgs in -- the guard' '#print axioms libsignal_core.address.ServiceId.kind_spec' \
    '#guard_msgs in' '#print axioms libsignal_core.address.ServiceId.helper' > "$tmp/r4d/$spec"
  expect pass "rule 4, trailing line comment after an active guard" "$tmp/r4d"

  if [ "$failed" -eq 0 ]; then echo "Self-test OK"; fi
  return "$failed"
}

if [ "${1:-}" = --self-test ]; then
  self_test
else
  check "${1:-.}"
  echo "Spec layout OK"
fi
