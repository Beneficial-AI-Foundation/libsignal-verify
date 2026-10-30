# Protocol models and correspondence

## Project layout

A single root Lake project and `lean-toolchain` govern all libraries. `Libsignal` uses `srcDir = "rust"`; its root `rust/Libsignal.lean` imports the extracted code and functional-correctness specifications. `Protocols.lean` is the separate root for local protocol models and correspondence.

`lake build Libsignal` builds the functional-correctness library independently of the `Protocols` target. Plain `lake build` builds all default targets.

Upstream `rust/bridge/` contains language bindings for C/Swift, Java/Kotlin and Node.js. It is separate from the protocol-model and correspondence library.

## File placement

Each protocol gets one folder under `Protocols/`, named after the protocol, holding both the abstract model and its realisation on the extracted code. Material staged for upstream libraries sits beside it.

| Path | Content |
| --- | --- |
| `Protocols/PQXDH/Model/` | abstract PQXDH model over generic primitives |
| `Protocols/PQXDH/` | the model at libsignal's primitives and the results on the extracted code |
| `Protocols/PQXDH/Realization/` | the Full realization: the UAKE scheme on the extracted entry points, its contracts, and its correctness and security statements |
| `Protocols/Realization/` | semantics shared by realizations: extracted code as an oracle computation that may fault |
| `Protocols/Specs/` | spec summaries: `recall` restatements and axiom checks that freeze the headline statements |
| `Protocols/ToVCVio/` | definitions and lemmas staged for VCVio |
| `Protocols/ToMathlib.lean` | lemmas staged for Mathlib |
| `ProtocolsTest/` | fixtures and tests for the `Protocols` library, built by default but not part of it |
| `Protocols/LEDGER.md` | axiom closures of the endpoint declarations and the list of admitted lemmas, with the commands that regenerate them |
| `rust/Libsignal/Spec/` | functional-correctness specifications of extracted functions |

Files ported from other projects keep their own licence and are listed in `Protocols/ATTRIBUTION.md`.

A `recall` restatement in a spec summary is checked up to definitional equality: it fails when a statement
changes its meaning, but not when it only changes its spelling or the names of its binders.
