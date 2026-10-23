/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs
import Libsignal.Spec.Protocol.Crypto.HkdfSha256

/-! # Spec Theorem for `HandshakeKeys::derive_with_label`

Specification and proof for `libsignal_protocol.pqxdh.HandshakeKeys.derive_with_label`, which
turns the PQXDH shared secret material into the keys that initialise the ratchets.

The function runs HKDF-SHA256 with no salt, the secret material as input keying material and
the label as `info`, producing 96 bytes. It splits these bytes into three consecutive 32-byte
keys: the root key, the chain key (with chain index zero) and the initial key of the
post-quantum ratchet (PQR).

HKDF itself is opaque in the extraction. The theorem is parametric in a supplied MAC interface
`H : HmacSha256` (assumed, not proved, to be HMAC-SHA256). It assumes `HkdfSha256Contract H`
and proves, under that assumption only, that the extracted code succeeds and returns the three
slices of the RFC 5869 output `hkdfSha256Okm96 H none secret_input label` computed from `H`. It
says nothing about which function `H` is, about the security of HKDF, or about how the keys are
used later.

**Source**: rust/protocol/src/pqxdh.rs, lines 79:4-96:5. For extraction, the upstream
`derive_arrays` helper is replaced by an explicit 96-byte buffer and three 32-byte copies with
the same HKDF call, label, `expect` and chain index (see `extraction-notes.md`).
-/

open Aeneas Aeneas.Std Result
open libsignal_protocol.crypto (HmacSha256 HkdfSha256Contract hkdfSha256Okm96)
open libsignal_protocol.ratchet.keys (RootKey ChainKey)

namespace libsignal_protocol.pqxdh.HandshakeKeys

open Aeneas.Std.core.result.Result (expect) in
/-- `Result::expect` returns the payload of an `Ok`. -/
private theorem expect_ok {T E : Type} (inst : core.fmt.Debug E) (x : T) (msg : Str) :
    expect inst (.Ok x) msg = ok x := rfl

/-
natural language description:

• Allocates a zeroed 96-byte buffer `bytes` and lends it to
  `crypto::hkdf_sha256(None, secret_input, label, &mut bytes)`, then calls `expect` on the
  result, which panics on an `Err`.
• Allocates three zeroed 32-byte arrays and copies `bytes[..32]`, `bytes[32..64]` and
  `bytes[64..]` into them with `copy_from_slice`, which panics on a length mismatch.
• Returns `HandshakeKeys` with root key `RootKey::new(bytes[..32])`, chain key
  `ChainKey::new(bytes[32..64], 0)` and PQR key `bytes[64..]`.

natural language specs:

• For a supplied MAC interface `H`, assume `hkdf_sha256` meets `HkdfSha256Contract H`, and let
  `okm = hkdfSha256Okm96 H none secret_input label` be the RFC 5869 output computed from `H`.
• The function succeeds for every `label` and `secret_input`.
• The root key is `okm[0..32)`, the chain key is `okm[32..64)` with chain index `0`, and the
  PQR key is `okm[64..96)`.
-/

/-- **Spec and proof concerning `pqxdh.HandshakeKeys.derive_with_label`**:
for any MAC interface `H` and under `HkdfSha256Contract H`, the function succeeds and splits
the 96-byte RFC 5869 output computed from `H`,
`okm` into root key `okm[0..32)`, chain key `okm[32..64)` with index `0`, and PQR key
`okm[64..96)`. -/
@[step]
theorem derive_with_label_spec (H : HmacSha256) (h_hkdf : HkdfSha256Contract H)
    (label secret_input : Slice Std.U8) :
    derive_with_label label secret_input ⦃ (keys : pqxdh.HandshakeKeys) =>
      let okm := hkdfSha256Okm96 H none secret_input.val label.val
      (keys.root_key.key).val = okm.slice 0 32 ∧
      (keys.chain_key.key).val = okm.slice 32 64 ∧
      keys.chain_key.index = 0#u32 ∧
      keys.pqr_key.val = okm.slice 64 96 ⦄ := by
  unfold derive_with_label
  step*
  step with crypto.hkdf_sha256_okm96_spec h_hkdf
  subst r_post
  simp only [expect_ok]
  step*
  simp only [RootKey.new, ChainKey.new]
  step*
  have h_s1 : (↑s1 : List U8).length = 96 := by
    simpa [Slice.length, s_post] using r_post1
  have h_back : ((Array.repeat 96#usize 0#u8).from_slice s1).val = s1.val :=
    Array.from_slice_val _ _ (by simp [h_s1])
  have h_okm : (hkdfSha256Okm96 H none secret_input.val label.val).length = 96 := by
    rw [← r_post2]; exact h_s1
  split_conjs
  · simp [*]
  · have h_s6 : ((Array.repeat 32#usize 0#u8).from_slice s6).val = s6.val :=
      Array.from_slice_val _ _ (by simpa [Slice.length] using s6_post1)
    simp [*]
  · simp [*, List.slice]

end libsignal_protocol.pqxdh.HandshakeKeys
