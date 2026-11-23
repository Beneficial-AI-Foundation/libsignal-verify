/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Core.Funs
import Libsignal.Proofs.Std.Alloc.Vec.ExtendFromSlice
import Libsignal.Proofs.Std.Alloc.Boxed.Convert

/-! # Spec theorem for `curve::PublicKey::serialize`

A serialized curve25519 public key is the key-type byte followed by the 32 bytes of the key. The
only key type is Djb. Its byte is `5`. `serialize_spec` states the bytes that serialization
returns. The Full realization of PQXDH serializes the same keys twice, once to sign them and once
to verify the signature, so it needs only that the call succeeds. The statement gives the bytes, as
`libsignal_protocol.kem.Ciphertext.serialize_spec` does for ciphertexts.

**Source**: rust/core/src/curve.rs, lines 122:4-132:5 (`PublicKey::serialize`) of the work copy
that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_core.curve.PublicKey

/-
natural language description:

• Reads the 32 bytes of the key, allocates a vector, pushes the key-type byte `5`, appends the
  bytes of the key, and converts the vector to a boxed slice.

natural language specs:

• The call succeeds, and for a Djb key with the bytes `v` it returns the byte `5` followed by the
  bytes `v`.
-/

/-- **Spec theorem for `curve.PublicKey.serialize`**: serialization of a Djb public key with the
bytes `v` returns the key-type byte `5` followed by the bytes `v`. -/
@[step]
theorem serialize_spec (pk : curve.PublicKey) :
    curve.PublicKey.serialize pk ⦃ s =>
      ∀ v, pk.key = .DjbPublicKey v → s.val = 5#u8 :: v.val ⦄ := by
  obtain ⟨⟨v0⟩⟩ := pk
  have hkt : curve.PublicKey.key_type { key := .DjbPublicKey v0 } = ok curve.KeyType.Djb := rfl
  have hv : curve.KeyType.value curve.KeyType.Djb = ok 5#u8 := rfl
  open alloc.vec in
  have hcap : ∀ j, (Vec.with_capacity U8 j).val = [] := fun _ => rfl
  open core.clone in
  have h_clone : ∀ x ∈ v0.val, CloneU8.clone x = ok x := fun _ _ => rfl
  unfold curve.PublicKey.serialize
  step*
  simp only [hkt, hv]
  step*

end libsignal_core.curve.PublicKey
