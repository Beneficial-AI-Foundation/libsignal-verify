#!/usr/bin/env bash
# Check the dependency rule of Protocols/README.md: no file under Protocols/Models/ imports the
# extraction (`Libsignal`) or a realisation (`Protocols.<P>`, `Protocols.Realization`). Within the
# Protocols library, a model may import only `Protocols.Models`, `Protocols.ToVCVio` and
# `Protocols.ToMathlib`; outside it, Mathlib and VCVio are allowed.
#
# The check is scripts/ModelsDependencyCheck.lean. It reads each import header with Lean's own
# header parser, so it needs the Lean toolchain of lean-toolchain but no build.
#
# Run from the repository root:
#   scripts/models-dependency-check.sh [ROOT]   checks ROOT/Protocols/Models (ROOT defaults to .)
#   scripts/models-dependency-check.sh --self-test
#                                               checks the rule on passing and failing headers
set -euo pipefail

exec lean --run "$(dirname "$0")/ModelsDependencyCheck.lean" "$@"
