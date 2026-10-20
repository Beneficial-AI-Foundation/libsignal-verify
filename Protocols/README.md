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
| `Protocols/ToVCVio/` | definitions and lemmas staged for VCVio |
| `Protocols/ToMathlib.lean` | lemmas staged for Mathlib |
| `ProtocolsTest/` | fixtures and tests for the `Protocols` library, built by default but not part of it |
| `rust/Libsignal/Spec/` | functional-correctness specifications of extracted functions |

Files ported from other projects keep their own licence and are listed in `Protocols/ATTRIBUTION.md`.
