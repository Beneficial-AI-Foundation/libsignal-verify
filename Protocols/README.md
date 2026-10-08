# Protocol models and correspondence

## Project layout

A single root Lake project and `lean-toolchain` govern both libraries. `Libsignal` uses `srcDir = "rust"`; its root `rust/Libsignal.lean` imports the extracted code and functional-correctness specifications. `Protocols.lean` is the separate root for local protocol models and correspondence. It has no model imports.

`lake build Libsignal` builds the functional-correctness library independently of the `Protocols` target. Plain `lake build` builds both default targets.

Upstream `rust/bridge/` contains language bindings for C/Swift, Java/Kotlin and Node.js. It is separate from the protocol-model and correspondence library.

## File placement

Place abstract theory under `Protocols/Models/`, protocol correspondence under named siblings such as `Protocols/PQXDH/`, and specifications of extracted functions under `rust/Libsignal/Spec/`.
