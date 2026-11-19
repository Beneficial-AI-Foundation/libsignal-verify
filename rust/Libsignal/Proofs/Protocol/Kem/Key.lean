/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs
import Libsignal.Proofs.Protocol.Kem.Ciphertext

/-! # Spec theorem for `kem::Key::serialize`

A serialized KEM key is the key-type byte followed by the bytes of the key material. In the
reviewed extraction, Kyber1024 is the only key type, and its wire byte is `0x08`. Production Rust
also has Kyber768 (`0x07`) and ML-KEM 1024 (`0x0A`) behind features that the extraction does not
enable. `serialize_spec` states the bytes that serialization returns, for a key of either kind. The
Full realization of PQXDH serializes Bob's Kyber public keys, so it needs that the call succeeds on
a key whose material has fewer than `Usize.max` bytes. The statement gives the bytes, as
`libsignal_protocol.kem.Ciphertext.serialize_spec` does for ciphertexts.

**Source**: rust/protocol/src/kem.rs, lines 346:4-351:5 (`Key::serialize`) of the work copy that
Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.kem.Key

/-
natural language description:

• Allocates a vector, pushes the key-type byte `8`, appends the bytes of the key material, and
  converts the vector to a boxed slice.

natural language specs:

• If the key material has fewer than `Usize.max` bytes, the call succeeds and returns the byte `8`
  followed by the bytes of the key material.
-/

/-- **Spec theorem for `kem.Key.serialize`**: serialization of a key whose material has fewer than
`Usize.max` bytes returns the key-type byte `8` followed by the bytes of the key material. -/
@[step]
theorem serialize_spec {T : Type} (inst : kem.KeyKind T) (k : kem.Key T)
    (h : (k.key_data.data).length < Usize.max) :
    kem.Key.serialize inst k ⦃ s => s.val = 8#u8 :: (k.key_data.data).val ⦄ := by
  have e : kem.Key.serialize inst k = kem.Ciphertext.serialize ⟨k.key_type, k.key_data.data⟩ := by
    open kem.KeyMaterial.Insts in
    simp [kem.Key.serialize, kem.Ciphertext.serialize, CoreOpsDerefDerefSliceU8.deref]
  rw [e]
  exact Ciphertext.serialize_spec _ h

end libsignal_protocol.kem.Key
