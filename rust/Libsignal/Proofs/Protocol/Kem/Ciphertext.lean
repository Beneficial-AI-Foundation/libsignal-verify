/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs
import Libsignal.Proofs.Std.Alloc.Vec.ExtendFromSlice
import Libsignal.Proofs.Std.Alloc.Boxed.Convert

/-! # Spec theorems for `kem::Ciphertext::serialize` and `kem::Ciphertext::deserialize`

A serialized KEM ciphertext is the key-type byte followed by the bytes of the ciphertext. The only
key type is Kyber1024. Its byte is `8`, and a Kyber1024 ciphertext has 1568 bytes. `serialize_spec`
states the bytes that serialization returns. `deserialize_spec` states that deserialization of such
bytes returns the ciphertext. Together they give the round trip between
`kem::Key<Public>::encapsulate` and `kem::Key<Secret>::decapsulate` that an honest PQXDH run needs.

**Source**: rust/protocol/src/kem.rs, lines 520:4-540:5 (`Ciphertext::deserialize`) and
543:4-548:5 (`Ciphertext::serialize`) of the work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.kem.Ciphertext

/-
natural language description:

• Allocates a vector, pushes the key-type byte `8`, appends the bytes of the ciphertext, and
  converts the vector to a boxed slice.

natural language specs:

• If the ciphertext has fewer than `Usize.max` bytes, the call succeeds and returns the byte `8`
  followed by the bytes of the ciphertext.
-/

/-- **Spec theorem for `kem.Ciphertext.serialize`**: serialization of a ciphertext with fewer than
`Usize.max` bytes returns the key-type byte `8` followed by the bytes of the ciphertext. -/
@[step]
theorem serialize_spec (ct : kem.Ciphertext) (h : ct.data.length < Usize.max) :
    kem.Ciphertext.serialize ct ⦃ s => s.val = 8#u8 :: ct.data.val ⦄ := by
  have hv : kem.KeyType.value ct.key_type = ok 8#u8 := rfl
  have hcap : ∀ j, (alloc.vec.Vec.with_capacity U8 j).val = [] := fun _ => rfl
  have h_clone : ∀ x ∈ ct.data.val, core.clone.CloneU8.clone x = ok x := fun _ _ => rfl
  unfold kem.Ciphertext.serialize
  step*
  simp only [hv]
  step*

/-
natural language description:

• Rejects an empty input, reads the key-type byte, rejects an unknown type and a wrong total
  length, and returns the Kyber1024 ciphertext made of the bytes after the first one.

natural language specs:

• If the input is the byte `8` followed by 1568 bytes `data`, the call succeeds and returns the
  Kyber1024 ciphertext with the bytes `data`.
-/

/-- **Spec theorem for `kem.Ciphertext.deserialize`**: deserialization of the byte `8` followed by
the 1568 bytes `data` returns the Kyber1024 ciphertext with the bytes `data`. -/
theorem deserialize_spec (value data : Slice Std.U8) (hs : value.val = 8#u8 :: data.val)
    (hlen : data.length = 1568) :
    kem.Ciphertext.deserialize value ⦃ r =>
      r = .Ok { key_type := .Kyber1024, data := data } ⦄ := by
  have hsl : value.length = 1569 := by
    simp only [Slice.length, hs, List.length_cons]
    have : data.val.length = 1568 := hlen
    omega
  have hCL : kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.CIPHERTEXT_LENGTH =
      1568#usize := by
    unfold kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.CIPHERTEXT_LENGTH
      libcrux_ml_kem.types.MlKemCiphertext.Insts.Libsignal_protocolKemConstantLength.LENGTH
    rfl
  have htry : kem.KeyType.Insts.CoreConvertTryFromU8SignalProtocolError.try_from 8#u8 =
      ok (core.result.Result.Ok kem.KeyType.Kyber1024) := rfl
  unfold kem.Ciphertext.deserialize
  step*
  have hi : i = 8#u8 := by simp [i_post, hs]
  subst hi
  simp only [htry, core.result.Result.Insts.CoreOpsTry.branch, hCL]
  step*
  have h2 : s.val = value.val.drop 1 := by assumption
  have h3 : s.val = v.val := by rw [s_post]; rfl
  have hs1 : s1 = data := by
    apply Slice.ext
    rw [s1_post1, ← h3, h2, hs]
    rfl
  rw [hs1]

end libsignal_protocol.kem.Ciphertext
