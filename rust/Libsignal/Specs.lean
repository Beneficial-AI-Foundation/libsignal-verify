import Libsignal.Specs.Core.Address
import Libsignal.Specs.Protocol.Crypto
import Libsignal.Specs.Protocol.Pqxdh
import Libsignal.Specs.Std.Alloc.Boxed
import Libsignal.Specs.Std.Alloc.Vec
import Libsignal.Specs.Std.Core.Array

/-!
# Spec summaries of the functional-correctness specifications

One summary per Rust source file, at the corresponding path: `Specs/Core/Address.lean` covers
`rust/core/src/address.rs`, and `Specs/Std/<crate>/...` covers a Rust standard-library file.
Each summary restates with `recall` every public theorem of `Libsignal.Proofs` about that file's
items, so a reader can check the statements apart from the proofs. The build rejects a statement
change beyond definitional equality, so a change of spelling or of binder names alone passes.
`#guard_msgs` rejects a change to the axioms of any theorem or definition.

`Proofs/Core/SharedTypes.lean` holds only `example`s that check type identifications, so it has no
summary.
-/
