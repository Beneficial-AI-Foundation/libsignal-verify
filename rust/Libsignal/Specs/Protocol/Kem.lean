/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Protocol.Kem.Ciphertext

/-!
# Spec summary: `rust/protocol/src/kem.rs`

This file freezes the specifications of the items of `rust/protocol/src/kem.rs`. Each theorem is
restated with `recall` and has a `#guard_msgs` check on the axioms it depends on.

The two theorems cover the serialization and the deserialization of a Kyber1024 ciphertext.
The closure of `deserialize_spec` has two axioms of the extraction besides the logical axioms of
Lean, `core.num.niche_types.NonZeroU8Inner` and `core.num.nonzero.NonZero`. Both are also in the
closures of the two entry points.
-/

/-! ## `Ciphertext::serialize` and `Ciphertext::deserialize` -/

open Aeneas Aeneas.Std Result libsignal_protocol in
recall libsignal_protocol.kem.Ciphertext.serialize_spec (ct : kem.Ciphertext)
    (h : ct.data.length < Usize.max) :
    kem.Ciphertext.serialize ct ⦃ s => s.val = 8#u8 :: ct.data.val ⦄

/--
info: 'libsignal_protocol.kem.Ciphertext.serialize_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.kem.Ciphertext.serialize_spec

open Aeneas Aeneas.Std Result libsignal_protocol in
recall libsignal_protocol.kem.Ciphertext.deserialize_spec (value data : Slice Std.U8)
    (hs : value.val = 8#u8 :: data.val) (hlen : data.length = 1568) :
    kem.Ciphertext.deserialize value ⦃ r =>
      r = .Ok { key_type := .Kyber1024, data := data } ⦄

/--
info: 'libsignal_protocol.kem.Ciphertext.deserialize_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.kem.Ciphertext.deserialize_spec
