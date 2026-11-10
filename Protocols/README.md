# Protocol models and correspondence

## Project layout

A single root Lake project and `lean-toolchain` govern all libraries. `Libsignal` uses `srcDir = "rust"`; its root `rust/Libsignal.lean` imports the extracted code and functional-correctness specifications. `Protocols.lean` is the separate root for local protocol models and correspondence.

`lake build Libsignal` builds the functional-correctness library independently of the `Protocols` target. Plain `lake build` builds all default targets.

Upstream `rust/bridge/` contains language bindings for C/Swift, Java/Kotlin and Node.js. It is separate from the protocol-model and correspondence library.

## File placement

The `Protocols` library keeps the theory of a protocol apart from its realisation on the extracted code. For a protocol `<P>`, such as PQXDH:

| Path | Namespace | Content |
| --- | --- | --- |
| `Protocols/Models/<P>/` | `Protocols.Models.<P>` | the models library: the abstract model of `<P>` over generic primitives, with its correctness and security |
| `Protocols/<P>/` | `Protocols.<P>` | the realisation of `<P>` on the extracted code: its scheme, contracts, and correctness and security statements |
| `Protocols/Realization/` | `Protocols.Realization` | infrastructure that the realisations of several protocols share, such as `RustOracleComp` |
| `Protocols/ToVCVio/`, `Protocols/ToMathlib.lean` | as in VCVio and Mathlib | the shared foundation: definitions and lemmas staged for VCVio and Mathlib |
| `Protocols/Specs/` | | spec summaries that freeze the headline statements with `recall` and dependency checks; `Protocols/Specs/<P>.lean` covers `Protocols/<P>/`, and `Protocols/Specs/Models/<P>.lean` the endpoint theorems of `Protocols/Models/<P>/` |

Files outside these folders:

| Path | Content |
| --- | --- |
| `ProtocolsTest/` | fixtures and tests for the `Protocols` library, at the paths of the modules they test (`ProtocolsTest/<P>/` for a realisation); built by default but not part of the library |
| `Protocols/LEDGER.md` | axiom closures of the endpoint declarations and the list of admitted lemmas, with the commands that regenerate them |
| `Protocols/ATTRIBUTION.md` | the files ported from other projects, which keep their own licence |
| `rust/Libsignal/Proofs/` | functional-correctness specifications of extracted functions, with their proofs |
| `rust/Libsignal/Specs/` | spec summaries of `rust/Libsignal/Proofs/`, one per Rust source file |

The dependency rule: no file under `Protocols/Models/` imports the extraction (`Libsignal`) or a realisation (`Protocols.<P>`, `Protocols.Realization`). Inside the `Protocols` library, a model imports only `Protocols.Models`, `Protocols.ToVCVio` and `Protocols.ToMathlib`. A realisation may import the models. CI checks the rule with `scripts/models-dependency-check.sh`. The check reads each import header with Lean's own header parser, so comments, line breaks, `public`, `meta` and `import all` count as they do for Lean. CI first runs a self-test of the check on fixed headers.

A `recall` restatement in a spec summary is checked up to definitional equality: it fails when a statement
changes its meaning, but not when it only changes its spelling or the names of its binders.
