# Protocol models and correspondence

## Project layout

A single root Lake project and `lean-toolchain` govern both libraries. `Libsignal` uses `srcDir = "rust"`; its root `rust/Libsignal.lean` imports the extracted code and functional-correctness specifications. `Protocols.lean` is the separate root for local protocol models and correspondence. It has no model imports.

`lake build Libsignal` builds the functional-correctness library independently of the `Protocols` target. Plain `lake build` builds both default targets.

Upstream `rust/bridge/` contains language bindings for C/Swift, Java/Kotlin and Node.js. It is separate from the protocol-model and correspondence library.

## File placement

The layout follows SPQR-verify PR #503. Each protocol gets one folder under `Protocols/`, named after the protocol, holding both the abstract model and its realisation on the extracted code. Material staged for upstream libraries sits beside it.

| Path | Content |
| --- | --- |
| `Protocols/PQXDH/Model/` | abstract PQXDH model over generic primitives |
| `Protocols/PQXDH/Model/LibsignalPQXDH/` | the model instantiated with libsignal's primitives |
| `Protocols/PQXDH/Contract.lean`, `Contract/Primitives.lean` | the extracted operations as instances of the model |
| `Protocols/PQXDH/Correctness/`, `Correct.lean`, `WellFormed.lean`, `Secure.lean` | correctness, well-formedness and security results on the extracted code |
| `Protocols/ToVCVio/` | definitions and lemmas staged for VCVio |
| `Protocols/ToMathlib.lean` | lemmas staged for Mathlib |
| `rust/Libsignal/Spec/` | functional-correctness specifications of extracted functions |

Namespaces follow the paths (`Protocols.PQXDH`, `Protocols.PQXDH.LibsignalPQXDH`). Lemmas relating an extracted operation to the model are named `..._toModel`.
