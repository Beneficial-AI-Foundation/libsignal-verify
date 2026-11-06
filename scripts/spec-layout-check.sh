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
#
# Run from the repository root:
#   scripts/spec-layout-check.sh [ROOT]   checks ROOT/rust/Libsignal (ROOT defaults to .)
#   scripts/spec-layout-check.sh --self-test
#                                         checks that each rule passes a good tree and fails a
#                                         tree with one planted violation
set -euo pipefail

check() {
  local root=$1
  local lib=$root/rust/Libsignal
  local proofs=$lib/Proofs specs=$lib/Specs
  local status=0

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

  local file rel dir summary name
  while IFS= read -r -d '' file; do
    rel=${file#"$proofs"/}
    local theorems defs
    theorems=$(grep -E '^(theorem|lemma)[[:space:]]' "$file" | awk '{print $2}' || true)
    defs=$(grep -E '^(noncomputable[[:space:]]+)?(def|abbrev|structure)[[:space:]]' "$file" \
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
    for name in $theorems; do
      if ! grep -qE "^recall[[:space:]]+([^[:space:]]*\.)?${name##*.}([[:space:]]|$)" "$summary"
      then
        echo "Theorem $name of Proofs/$rel is not recalled in ${summary#"$lib"/}"
        status=1
      fi
    done
    for name in $defs; do
      if ! grep -qE "^#print axioms[[:space:]]+([^[:space:]]*\.)?${name##*.}$" "$summary"; then
        echo "Definition $name of Proofs/$rel has no axiom check in ${summary#"$lib"/}"
        status=1
      fi
    done
  done < <(find "$proofs" -name '*.lean' -print0)

  while IFS= read -r -d '' file; do
    for name in $(grep -E '^recall[[:space:]]' "$file" | awk '{print $2}'); do
      if ! grep -qxF "#print axioms $name" "$file"; then
        echo "Recalled $name has no axiom check in ${file#"$lib"/}"
        status=1
      fi
    done
    local unguarded
    unguarded=$(awk '/^#print axioms/ && prev !~ /^#guard_msgs/ {print FILENAME ":" FNR ": " $0}
      {prev = $0}' "$file")
    if [ -n "$unguarded" ]; then
      echo "Axiom checks without #guard_msgs:"
      echo "$unguarded"
      status=1
    fi
  done < <(find "$specs" -name '*.lean' -print0)

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

  expect() {
    local want=$1 label=$2 r=$3
    if check "$r" > "$tmp/out" 2>&1; then got=pass; else got=fail; fi
    if [ "$got" != "$want" ]; then
      echo "SELF-TEST FAILED: $label: expected $want, got $got"
      cat "$tmp/out"
      failed=1
    fi
  }

  make_good "$tmp/good"
  expect pass "good tree" "$tmp/good"

  make_good "$tmp/r1"
  mkdir -p "$tmp/r1/rust/Libsignal/Proofs/Aeneas"
  expect fail "rule 1, tool-named directory" "$tmp/r1"

  make_good "$tmp/r2"
  echo 'recall Aeneas.Std.alloc.vec.Vec.foo : True' \
    >> "$tmp/r2/rust/Libsignal/Specs/Core/Address.lean"
  expect fail "rule 2, std item outside Std/" "$tmp/r2"

  make_good "$tmp/r3a"
  rm "$tmp/r3a/rust/Libsignal/Specs/Core/Address.lean"
  expect fail "rule 3, no summary" "$tmp/r3a"

  make_good "$tmp/r3b"
  echo 'theorem raw_uuid_spec : True := trivial' \
    >> "$tmp/r3b/rust/Libsignal/Proofs/Core/Address/Kind.lean"
  expect fail "rule 3, theorem not recalled" "$tmp/r3b"

  make_good "$tmp/r3c"
  echo 'abbrev Bytes : Type := Nat' >> "$tmp/r3c/rust/Libsignal/Proofs/Core/Address/Kind.lean"
  expect fail "rule 3, definition without axiom check" "$tmp/r3c"

  make_good "$tmp/r4a"
  printf '%s\n' 'recall libsignal_core.address.ServiceId.other : True' \
    >> "$tmp/r4a/rust/Libsignal/Specs/Core/Address.lean"
  expect fail "rule 4, recall without axiom check" "$tmp/r4a"

  make_good "$tmp/r4b"
  printf '%s\n' '#print axioms libsignal_core.address.ServiceId.kind' \
    >> "$tmp/r4b/rust/Libsignal/Specs/Core/Address.lean"
  expect fail "rule 4, axiom check without #guard_msgs" "$tmp/r4b"

  if [ "$failed" -eq 0 ]; then echo "Self-test OK"; fi
  return "$failed"
}

if [ "${1:-}" = --self-test ]; then
  self_test
else
  check "${1:-.}"
  echo "Spec layout OK"
fi
