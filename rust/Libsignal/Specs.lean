import Libsignal.Specs.Core.Address
import Libsignal.Specs.Protocol.Crypto
import Libsignal.Specs.Protocol.Pqxdh
import Libsignal.Specs.Std.Alloc.Boxed
import Libsignal.Specs.Std.Alloc.Vec

/-!
# Spec summaries of the functional-correctness specifications

One file per Rust source file, at the path of that source file: `Specs/Core/Address.lean` covers
`rust/core/src/address.rs`, and `Specs/Std/<crate>/...` covers a file of the Rust standard
library. Each file restates with `recall` every public theorem of `Libsignal.Proofs` about its
items. It also checks the axioms of each theorem and definition with `#guard_msgs`. The build
fails if a statement or its axioms change, so a reader can check the statements here without
reading the proofs.

`recall` checks a restatement up to definitional equality: it fails when a statement changes its
meaning, but not when it only changes its spelling or the names of its binders.

`Proofs/Core/SharedTypes.lean` holds only `example`s that check type identifications, so it has no
summary.
-/
