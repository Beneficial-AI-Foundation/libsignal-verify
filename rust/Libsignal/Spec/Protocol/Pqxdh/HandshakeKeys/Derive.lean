/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs
import Libsignal.Spec.Protocol.Pqxdh.HandshakeKeys.DeriveWithLabel

/-! # Spec Theorem for `HandshakeKeys::derive`

Specification and proof for `libsignal_protocol.pqxdh.HandshakeKeys.derive`, the PQXDH key
derivation. It calls `derive_with_label` with the fixed label
`WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024`, so its specification is the specification of
`derive_with_label` with `info` fixed to the 46 bytes of that label.

**Source**: rust/protocol/src/pqxdh.rs, lines 72:4-77:5
(`Self::derive_with_label(b"WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024", secret_input)`).
-/

open Aeneas Aeneas.Std Result
open libsignal_protocol.crypto (HmacSha256 HkdfSha256Contract hkdfSha256Okm96)

namespace libsignal_protocol.pqxdh.HandshakeKeys

/-- The PQXDH key-derivation label, `WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024`, as its
46 ASCII bytes. -/
def pqxdhKdfLabel : List Std.U8 :=
  [87#u8, 104#u8, 105#u8, 115#u8, 112#u8, 101#u8, 114#u8, 84#u8, 101#u8, 120#u8, 116#u8,
    95#u8, 88#u8, 50#u8, 53#u8, 53#u8, 49#u8, 57#u8, 95#u8, 83#u8, 72#u8, 65#u8, 45#u8, 50#u8,
    53#u8, 54#u8, 95#u8, 67#u8, 82#u8, 89#u8, 83#u8, 84#u8, 65#u8, 76#u8, 83#u8, 45#u8, 75#u8,
    89#u8, 66#u8, 69#u8, 82#u8, 45#u8, 49#u8, 48#u8, 50#u8, 52#u8]

/-- `pqxdhKdfLabel` is the UTF-8 (here ASCII) encoding of the label string. -/
theorem pqxdhKdfLabel_eq_utf8 :
    pqxdhKdfLabel.map (·.val) =
      ("WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8.toList.map (·.toNat)) := by
  decide +kernel

/-
natural language description:

• Builds the 46-byte array holding `WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024`,
  views it as a slice, and calls `derive_with_label(label, secret_input)`.

natural language specs:

• For a supplied MAC interface `H`, assume `hkdf_sha256` meets `HkdfSha256Contract H`, and let
  `okm = hkdfSha256Okm96 H none secret_input pqxdhKdfLabel`, the RFC 5869 output from `H`.
• The function succeeds for every `secret_input`.
• The root key is `okm[0..32)`, the chain key is `okm[32..64)` with chain index `0`, and the
  PQR key is `okm[64..96)`.
-/

/-- **Spec and proof concerning `pqxdh.HandshakeKeys.derive`**:
for any MAC interface `H` and under `HkdfSha256Contract H`, the function succeeds and splits the
96-byte RFC 5869 output computed from `H` for the PQXDH label into root key, chain key with
index `0`, and PQR key. -/
@[step]
theorem derive_spec (H : HmacSha256) (h_hkdf : HkdfSha256Contract H)
    (secret_input : Slice Std.U8) :
    derive secret_input ⦃ (keys : pqxdh.HandshakeKeys) =>
      let okm := hkdfSha256Okm96 H none secret_input.val pqxdhKdfLabel
      (keys.root_key.key).val = okm.slice 0 32 ∧
      (keys.chain_key.key).val = okm.slice 32 64 ∧
      keys.chain_key.index = 0#u32 ∧
      keys.pqr_key.val = okm.slice 64 96 ⦄ := by
  unfold derive
  step*
  have h_label : s.val = pqxdhKdfLabel := by
    simp [s_post, Array.to_slice, pqxdhKdfLabel]
  rw [h_label] at keys_post keys_post1 keys_post3
  exact ⟨keys_post, keys_post1, keys_post2, keys_post3⟩

end libsignal_protocol.pqxdh.HandshakeKeys
