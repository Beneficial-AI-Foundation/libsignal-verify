# Protocol models and correspondence

## Project layout

A single root Lake project and `lean-toolchain` govern both libraries. `Libsignal` uses `srcDir = "rust"`; its root `rust/Libsignal.lean` imports the extracted code and functional-correctness specifications. `Protocols.lean` is the separate root for protocol models and correspondence. This follows SPQR-verify's shared-project arrangement without duplicating dependency manifests under `rust/`.

`lake build Libsignal` builds the functional-correctness library independently of the `Protocols` target. Plain `lake build` builds both default targets.

Upstream `rust/bridge/` contains language bindings for C/Swift, Java/Kotlin and Node.js. It is separate from the implementation–model correspondence code under `Protocols/`.

## PQXDH compatibility

`Protocols.PQXDH.Compatibility` imports the local `Libsignal` translation together with the pinned VCVio library and the PQXDH model's security, correctness, well-formedness and transport modules. It deliberately avoids the model's umbrella, which also imports an older extracted implementation.

Build the named boundary with:

```sh
lake build Libsignal Protocols.PQXDH.Compatibility
```

The `#check` declarations establish that the intended endpoints are available in one Lean environment. They do not relate the extracted implementation to the abstract model. Imported security results retain upstream proof admissions; a successful build does not discharge them.

Place abstract theory under `Protocols/Models/`, protocol correspondence under named siblings such as `Protocols/PQXDH/`, and specifications of extracted functions under `rust/Libsignal/Spec/`. The canonical extraction currently covers Core, an AES-CBC provider and the two PQXDH roots. Production session/store orchestration, local ratchets and SPQR/Braid require separate implementation coverage.
