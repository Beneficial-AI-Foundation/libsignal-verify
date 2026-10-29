#!/usr/bin/env bash
# Check the layout rules for rust/Libsignal/Spec/ in CODING_GUIDELINES.md ("Lean specifications").
#
# 1. No directory under rust/Libsignal/Spec/ is named after a tool: Aeneas or Charon, in any case.
# 2. Standard-library specs live under rust/Libsignal/Spec/Std/. A .lean file outside Spec/Std/
#    fails if it opens a namespace rooted at `core`, `alloc` or `std`, or at `Aeneas.Std` (where the
#    extraction backend puts std items), or declares a name with one of those roots.
#
# Rule 2 is a namespace test. It cannot see a std item that the extraction places in a libsignal
# namespace, such as `libsignal_protocol.Box.Insts.CoreConvertAsRef` (in Spec/Std/Alloc/Boxed/).
# The rule that spec paths mirror the Rust source is not checked.
#
# Run from the repository root: scripts/spec-layout-check.sh
set -euo pipefail

spec=rust/Libsignal/Spec
status=0

tool_dirs=$(find "$spec" -type d \( -iname aeneas -o -iname charon \))
if [ -n "$tool_dirs" ]; then
  echo "Directories named after a tool:"
  echo "$tool_dirs"
  status=1
fi

std_root='(Aeneas\.Std|core|alloc|std)(\.|[[:space:]]|$)'
misplaced=$(find "$spec" -name '*.lean' -not -path "$spec/Std/*" -print0 \
  | xargs -0 grep -HnE "^[[:space:]]*(namespace|theorem|lemma|def|abbrev|instance)[[:space:]]+$std_root" \
  || true)
if [ -n "$misplaced" ]; then
  echo "Standard-library specs outside $spec/Std/:"
  echo "$misplaced"
  status=1
fi

[ "$status" -eq 0 ] && echo "Spec layout OK"
exit "$status"
