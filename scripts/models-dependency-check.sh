#!/usr/bin/env bash
# Check the dependency rule of Protocols/README.md: no file under Protocols/Models/ imports the
# extraction (`Libsignal`) or a realisation (`Protocols.<P>`, `Protocols.Realization`). Within the
# Protocols library, a model may import only `Protocols.Models`, `Protocols.ToVCVio` and
# `Protocols.ToMathlib`; outside it, Mathlib and VCVio are allowed.
#
# Run from the repository root:
#   scripts/models-dependency-check.sh [ROOT]   checks ROOT/Protocols/Models (ROOT defaults to .)
#   scripts/models-dependency-check.sh --self-test
#                                               checks the rule on passing and failing fixtures
set -euo pipefail

import='((public|meta|private)[[:space:]]+)*import[[:space:]]+'
end='(\.|[[:space:]]|$)'
watched="^[[:space:]]*${import}(Libsignal|Protocols)${end}"
allowed=":[0-9]+:[[:space:]]*${import}Protocols\.(Models|ToVCVio|ToMathlib)${end}"

check() {
  local models="$1/Protocols/Models"
  if [ ! -d "$models" ]; then
    echo "No directory $models"
    return 1
  fi
  local hits
  hits=$(grep -rnE --include='*.lean' "$watched" "$models" | grep -vE "$allowed" || true)
  if [ -n "$hits" ]; then
    echo "Protocols/Models/ imports the extraction or a realisation:"
    echo "$hits"
    return 1
  fi
  echo "Models dependency rule OK"
}

# Writes one Lean file with the given lines under ROOT/Protocols/Models/X/.
fixture() {
  local root=$1
  shift
  mkdir -p "$root/Protocols/Models/X"
  printf '%s\n' "$@" > "$root/Protocols/Models/X/A.lean"
}

self_test() {
  local dir status=0
  dir=$(mktemp -d)
  fixture "$dir/good" 'import Mathlib.Data.Fintype.Basic' 'import VCVio.OracleComp.OracleComp' \
    'import Protocols.ToVCVio' 'import Protocols.ToMathlib' 'import Protocols.Models.PQXDH.Basic' \
    '/-! Docs may name Protocols.PQXDH.Scheme. -/'
  fixture "$dir/libsignal" 'import Protocols.ToVCVio' 'import Libsignal.Translated.Protocol.Funs'
  fixture "$dir/realisation" 'import Protocols.PQXDH.Scheme'
  fixture "$dir/other-protocol" 'import Protocols.X3DH.Scheme'
  fixture "$dir/horizontal" 'import Protocols.Realization.RustOracleComp'
  fixture "$dir/specs" 'import Protocols.Specs.PQXDH'
  fixture "$dir/umbrella" 'import Protocols'
  fixture "$dir/public" 'public import Protocols.PQXDH.Defs'
  if ! check "$dir/good" > /dev/null; then
    echo "self-test: the passing fixture was rejected"
    status=1
  fi
  for bad in libsignal realisation other-protocol horizontal specs umbrella public; do
    if check "$dir/$bad" > /dev/null; then
      echo "self-test: the failing fixture '$bad' was accepted"
      status=1
    fi
  done
  rm -rf "$dir"
  [ "$status" -eq 0 ] && echo "Models dependency self-test OK"
  return "$status"
}

if [ "${1:-}" = "--self-test" ]; then
  self_test
else
  check "${1:-.}"
fi
