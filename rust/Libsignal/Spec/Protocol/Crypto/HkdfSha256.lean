/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.FunsExternal

/-! # HKDF-SHA256 and the contract for `crypto::hkdf_sha256`

The Rust helper `libsignal_protocol::crypto::hkdf_sha256` is extracted as the opaque declaration
`crypto.hkdf_sha256`: Aeneas does not translate the `hkdf` crate, so Lean knows only its type.
This file states what the helper is assumed to compute, in two layers. Everything here is
parametric in a supplied MAC interface `H`.

* **MAC interface.** HMAC-SHA256 is not defined here. `HmacSha256` is an assumed HMAC-SHA256
  interface: a function on byte strings together with the single proved fact that its tags have
  32 bytes. Nothing in Lean identifies the function with HMAC (FIPS 198-1) over SHA-256
  (FIPS 180-4); that identification is external trust, stated in this documentation only. No
  security property (PRF, random oracle) is assumed.
* **HKDF (RFC 5869).** HKDF-Extract and HKDF-Expand are defined from the supplied interface,
  following the RFC exactly. Only the 96-byte output length used by PQXDH is defined, as three
  Expand blocks. The result is HKDF-SHA256 precisely when the supplied interface is HMAC-SHA256.

`HkdfSha256Contract H` connects the extracted helper to these definitions: on a 96-byte output
buffer and an absent salt, the helper succeeds, keeps the buffer length and writes the RFC 5869
output computed from `H`. It is a hypothesis of the theorems that use it, never an axiom, and it
says nothing about which function `H` is.

**Source**: rust/protocol/src/crypto.rs, lines 50:0-57:1
(`hkdf::Hkdf::<Sha256>::new(salt, input_key_material).expand(info, output)`); the `hkdf` 0.13.0
crate realises RFC 5869 over `Hmac<Sha256>`.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.crypto

/-- An assumed HMAC-SHA256 interface on byte strings.

`mac key msg` is intended to be the HMAC-SHA256 tag of `msg` under `key`. Keys and messages are
byte strings of any length, matching the slice interface of the Rust `hmac` crate. The structure
records only that tags have 32 bytes, the SHA-256 output length; it does not establish that `mac`
is HMAC-SHA256, which remains an external assumption about the supplied value. -/
structure HmacSha256 where
  /-- The tag of a message under a key. -/
  mac : List Std.U8 → List Std.U8 → List Std.U8
  /-- Every tag has 32 bytes, the SHA-256 output length. -/
  mac_length : ∀ key msg, (mac key msg).length = 32

/-- `HashLen` for SHA-256: the output length of the hash, in bytes. -/
def hashLen : Nat := 32

/-- The salt used when none is given: `HashLen` zero bytes (RFC 5869, Section 2.2). -/
def hkdfDefaultSalt : List Std.U8 := List.replicate hashLen 0#u8

/-- HKDF-Extract (RFC 5869, Section 2.2): `PRK = HMAC-Hash(salt, IKM)`.

The salt is the HMAC key and the input keying material is the HMAC message. An absent salt is
replaced by `hkdfDefaultSalt`. -/
def hkdfExtract (H : HmacSha256) (salt : Option (List Std.U8)) (ikm : List Std.U8) :
    List Std.U8 :=
  H.mac (salt.getD hkdfDefaultSalt) ikm

/-- One HKDF-Expand block (RFC 5869, Section 2.3): `T(i) = HMAC-Hash(PRK, T(i-1) | info | i)`,
where the counter `i` is a single byte. -/
def hkdfExpandBlock (H : HmacSha256) (prk prev info : List Std.U8) (i : Std.U8) :
    List Std.U8 :=
  H.mac prk (prev ++ info ++ [i])

/-- HKDF-Expand (RFC 5869, Section 2.3) for `L = 96` bytes.

Here `N = ⌈L / HashLen⌉ = 3`. Starting from the empty string `T(0)`, the blocks are
`T(1) = HMAC(PRK, info | 0x01)`, `T(2) = HMAC(PRK, T(1) | info | 0x02)` and
`T(3) = HMAC(PRK, T(2) | info | 0x03)`; the output is the first `L` bytes of `T(1) | T(2) | T(3)`.
Since each block has 32 bytes, no block is truncated (`hkdfExpand96_length`). -/
def hkdfExpand96 (H : HmacSha256) (prk info : List Std.U8) : List Std.U8 :=
  let t1 := hkdfExpandBlock H prk [] info 1#u8
  let t2 := hkdfExpandBlock H prk t1 info 2#u8
  let t3 := hkdfExpandBlock H prk t2 info 3#u8
  (t1 ++ t2 ++ t3).take 96

/-- RFC 5869 HKDF with 96 bytes of output, computed from the supplied interface `H`:
HKDF-Extract followed by HKDF-Expand. It is HKDF-SHA256 when `H` is HMAC-SHA256. -/
def hkdfSha256Okm96 (H : HmacSha256) (salt : Option (List Std.U8))
    (ikm info : List Std.U8) : List Std.U8 :=
  hkdfExpand96 H (hkdfExtract H salt ikm) info

/-- The 96-byte HKDF output has exactly 96 bytes. -/
theorem hkdfExpand96_length (H : HmacSha256) (prk info : List Std.U8) :
    (hkdfExpand96 H prk info).length = 96 := by
  simp [hkdfExpand96, hkdfExpandBlock, H.mac_length]

/-- **Contract for the opaque `crypto::hkdf_sha256` at 96 bytes without salt.**

The extracted declaration is the root-level `crypto.hkdf_sha256`. For every input keying
material `ikm`, every `info` and every output buffer `out` of 96 bytes, the call
`hkdf_sha256(None, ikm, info, out)`
- returns `Ok(())`, so the caller's `expect` cannot panic;
- returns a buffer of the same length as `out`, so writing it back into the caller's array keeps
  the written bytes (Aeneas models `&mut [u8]` by returning the new slice);
- fills the buffer with `hkdfSha256Okm96 H none ikm info`, whatever `out` contained before.

This is a trusted assumption that the opaque helper agrees with the RFC 5869 definitions above
for the given `H`, stated as a hypothesis. It does not discharge, and is independent of, the
assumption that `H` is HMAC-SHA256. -/
def HkdfSha256Contract (H : HmacSha256) : Prop :=
  ∀ (ikm info out : Slice Std.U8), out.length = 96 →
    crypto.hkdf_sha256 none ikm info out ⦃ r out' =>
      r = .Ok () ∧ out'.length = out.length ∧
        out'.val = hkdfSha256Okm96 H none ikm.val info.val ⦄

/-- The call specification provided by `HkdfSha256Contract`, in the form used by `step`.

This lemma is deliberately untagged and invoked explicitly, as in
`step with hkdf_sha256_okm96_spec h …`. -/
theorem hkdf_sha256_okm96_spec {H : HmacSha256} (h : HkdfSha256Contract H)
    (ikm info out : Slice Std.U8) (h_len : out.length = 96) :
    crypto.hkdf_sha256 none ikm info out ⦃ r out' =>
      r = .Ok () ∧ out'.length = out.length ∧
        out'.val = hkdfSha256Okm96 H none ikm.val info.val ⦄ := by
  unfold HkdfSha256Contract at h
  exact h ikm info out h_len

end libsignal_protocol.crypto
