/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.FunsExternal

/-! # HKDF-SHA256 and the contracts for `crypto::hkdf_sha256`

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
  following the RFC exactly. HKDF-Expand is defined for every output length (`hkdfExpand`, from
  the blocks `hkdfT`). The 96-byte output used by PQXDH also has its own definition, as three
  Expand blocks, and the two agree at 96 bytes (`hkdfSha256Okm_ninetySix`). The definitions are
  total. The result is HKDF-SHA256 when the supplied interface is HMAC-SHA256, the output has at
  most 255 · 32 = 8,160 bytes, and the input lengths are in `HkdfSha256Domain`, so that every
  SHA-256 input is defined. A standalone HKDF-Expand is RFC 5869's only when its PRK has at least
  32 bytes.

`HkdfSha256RfcContract H` connects the extracted helper to these definitions: for every optional
salt and every output buffer of at most 255 · 32 = 8,160 bytes, on input lengths that keep every
SHA-256 input below 2^61 bytes (`HkdfSha256Domain`), the helper succeeds, keeps the buffer length
and writes the RFC 5869 output computed from `H`. It is the assumption of this file.
`HkdfSha256Contract H`, the case of an absent salt and a 96-byte buffer that PQXDH uses, follows
from it (`hkdfSha256Contract_of_rfc`). Both are hypotheses of the theorems that use them, never
axioms, and neither says which function `H` is.

**Source**: rust/protocol/src/crypto.rs, lines 50:0-57:1 of the patched copy: the helper exists only
after `translation-patches/protocol-crypto-hkdf_sha256.patch`
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
Since each block has 32 bytes, no block is truncated (`hkdfExpand96_length`). RFC 5869 asks for a
PRK of at least `HashLen` bytes. The definition takes a `prk` of any length. -/
def hkdfExpand96 (H : HmacSha256) (prk info : List Std.U8) : List Std.U8 :=
  let t1 := hkdfExpandBlock H prk [] info 1#u8
  let t2 := hkdfExpandBlock H prk t1 info 2#u8
  let t3 := hkdfExpandBlock H prk t2 info 3#u8
  (t1 ++ t2 ++ t3).take 96

/-- RFC 5869 HKDF with 96 bytes of output, computed from the supplied interface `H`:
HKDF-Extract followed by HKDF-Expand. It is HKDF-SHA256 when `H` is HMAC-SHA256 and the input
lengths are in `HkdfSha256Domain`. -/
def hkdfSha256Okm96 (H : HmacSha256) (salt : Option (List Std.U8))
    (ikm info : List Std.U8) : List Std.U8 :=
  hkdfExpand96 H (hkdfExtract H salt ikm) info

/-- The 96-byte HKDF output has exactly 96 bytes. -/
theorem hkdfExpand96_length (H : HmacSha256) (prk info : List Std.U8) :
    (hkdfExpand96 H prk info).length = 96 := by
  simp [hkdfExpand96, hkdfExpandBlock, H.mac_length]

/-- The input lengths on which HKDF-SHA256 is defined: every SHA-256 input has fewer than
2^61 bytes (FIPS 180-4).

The `sha2` crate computes the length of a message in bits as a `u64`, so a message of 2^61 bytes
or more overflows it. HKDF-SHA256 hashes these messages: a salt longer than the 64-byte block,
which HMAC hashes into a key; in Extract, one 64-byte pad block followed by `ikm`;
in Expand, one 64-byte pad block, the 32-byte block before (none for the first block), `info` and
the one-byte counter, so at most `info` and 97 bytes. Every other SHA-256 input has at most
96 bytes.

The bound on `info` is one bound for every output length. It is sufficient, but not always
necessary: at output length 0 Expand does not hash `info`, and for an output of 1 to 32 bytes its
only block needs `info.length + 65 < 2 ^ 61`. From 33 to 8,160 bytes, the bound is the one that the
code needs. Above 8,160 bytes Expand returns an error before it hashes anything. -/
def HkdfSha256Domain (salt : Option (List Std.U8)) (ikm info : List Std.U8) : Prop :=
  (∀ s ∈ salt, s.length < 2 ^ 61) ∧ ikm.length + 64 < 2 ^ 61 ∧ info.length + 97 < 2 ^ 61

/-- **Contract for the opaque `crypto::hkdf_sha256` at 96 bytes without salt.**

The extracted declaration is the root-level `crypto.hkdf_sha256`. For every input keying
material `ikm`, every `info` and every output buffer `out` of 96 bytes, with `ikm` and `info`
in the domain `HkdfSha256Domain` with no salt, the call `hkdf_sha256(None, ikm, info, out)`
- returns `Ok(())`, so the caller's `expect` cannot panic;
- returns a buffer of the same length as `out`, so writing it back into the caller's array keeps
  the written bytes (Aeneas models `&mut [u8]` by returning the new slice);
- fills the buffer with `hkdfSha256Okm96 H none ikm info`, whatever `out` contained before.

It is the case of an absent salt and a 96-byte buffer of the general contract
`HkdfSha256RfcContract` below, and it follows from that contract by `hkdfSha256Contract_of_rfc`,
so it is not assumed on its own. The theorems that use it still take it as a hypothesis. It does
not discharge, and is independent of, the assumption that `H` is HMAC-SHA256. -/
def HkdfSha256Contract (H : HmacSha256) : Prop :=
  ∀ (ikm info out : Slice Std.U8), out.length = 96 →
    HkdfSha256Domain none ikm.val info.val →
    crypto.hkdf_sha256 none ikm info out ⦃ r out' =>
      r = .Ok () ∧ out'.length = out.length ∧
        out'.val = hkdfSha256Okm96 H none ikm.val info.val ⦄

/-- The call specification provided by `HkdfSha256Contract`, in the form used by `step`.

This lemma is deliberately untagged and invoked explicitly, as in
`step with hkdf_sha256_okm96_spec h …`. -/
theorem hkdf_sha256_okm96_spec {H : HmacSha256} (h : HkdfSha256Contract H)
    (ikm info out : Slice Std.U8) (h_len : out.length = 96)
    (h_dom : HkdfSha256Domain none ikm.val info.val) :
    crypto.hkdf_sha256 none ikm info out ⦃ r out' =>
      r = .Ok () ∧ out'.length = out.length ∧
        out'.val = hkdfSha256Okm96 H none ikm.val info.val ⦄ := by
  unfold HkdfSha256Contract at h
  exact h ikm info out h_len h_dom

/-! ## HKDF for every output length -/

/-- The HKDF-Expand blocks (RFC 5869, Section 2.3): `hkdfT H prk info n` is `T(n)`.

`T(0)` is the empty string, and `T(i + 1) = HMAC-Hash(PRK, T(i) | info | i + 1)`, where the counter
is a single byte. The byte is `i + 1` modulo 256, so these are RFC 5869's blocks for `n ≤ 255`, the
largest counter that the RFC allows, when `prk` has at least `HashLen` bytes. For `T(1)`,
`T(0)` is empty, so the message is `info` and the counter. -/
def hkdfT (H : HmacSha256) (prk info : List Std.U8) : Nat → List Std.U8
  | 0 => []
  | i + 1 => hkdfExpandBlock H prk (hkdfT H prk info i) info
      (⟨BitVec.ofNat 8 (i + 1)⟩ : Std.U8)

/-- HKDF-Expand (RFC 5869, Section 2.3) for an output of `L` bytes.

With `N = ⌈L / HashLen⌉`, the output is the first `L` bytes of `T(1) | T(2) | … | T(N)`.
RFC 5869 allows `L ≤ 255 · HashLen`, that is 8,160 bytes. The definition is total in `L`: above
that bound the counter byte wraps, and the result is no longer RFC 5869's. RFC 5869 also asks for a
PRK of at least `HashLen` bytes. The definition takes a `prk` of any length, and with a shorter one
the result is not RFC 5869's either. Every block has `HashLen` bytes, so the output has exactly `L`
bytes for every `L` (`hkdfExpand_length`). -/
def hkdfExpand (H : HmacSha256) (prk info : List Std.U8) (L : Nat) : List Std.U8 :=
  ((List.range ((L + hashLen - 1) / hashLen)).flatMap
    (fun i => hkdfT H prk info (i + 1))).take L

/-- RFC 5869 HKDF with `L` bytes of output, computed from the supplied interface `H`:
HKDF-Extract with the optional salt, followed by HKDF-Expand. It is HKDF-SHA256 when `H` is
HMAC-SHA256, `L ≤ 255 · HashLen`, and the salt, `ikm` and `info` are in `HkdfSha256Domain`. The
PRK is a tag of `H`, so it has `HashLen` bytes. The function is total, and gives a value on other
inputs too. -/
def hkdfSha256Okm (H : HmacSha256) (salt : Option (List Std.U8))
    (ikm info : List Std.U8) (L : Nat) : List Std.U8 :=
  hkdfExpand H (hkdfExtract H salt ikm) info L

/-- HKDF-Expand returns exactly `L` bytes, for every `L`. -/
theorem hkdfExpand_length (H : HmacSha256) (prk info : List Std.U8) (L : Nat) :
    (hkdfExpand H prk info L).length = L := by
  have hT : ∀ n, (hkdfT H prk info (n + 1)).length = hashLen := fun n => by
    simp [hkdfT, hkdfExpandBlock, H.mac_length, hashLen]
  unfold hkdfExpand
  rw [List.length_take, List.length_flatMap]
  simp only [hT, List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, hashLen]
  omega

/-- At 96 bytes, the HKDF output of every length is the three-block output `hkdfSha256Okm96`. -/
theorem hkdfSha256Okm_ninetySix (H : HmacSha256) (salt : Option (List Std.U8))
    (ikm info : List Std.U8) :
    hkdfSha256Okm H salt ikm info 96 = hkdfSha256Okm96 H salt ikm info := by
  simp [hkdfSha256Okm, hkdfSha256Okm96, hkdfExpand, hkdfExpand96, hashLen, List.range_succ, hkdfT]
  rfl

/-- **Contract for the opaque `crypto::hkdf_sha256`: RFC 5869 for every salt and every output
length up to 8,160 bytes, on the input lengths of `HkdfSha256Domain`.**

The extracted declaration is the root-level `crypto.hkdf_sha256`. For every optional salt, every
input keying material `ikm`, every `info` and every output buffer `out` of at most
255 · 32 = 8,160 bytes, with the salt, `ikm` and `info` in the domain `HkdfSha256Domain`, the
call `hkdf_sha256(salt, ikm, info, out)`
- returns `Ok(())`;
- returns a buffer of the same length as `out` (Aeneas models `&mut [u8]` by returning the new
  slice);
- fills the buffer with `hkdfSha256Okm H salt ikm info out.length`, whatever `out` contained
  before. A present salt, the empty one included, is the HMAC key as given; an absent salt is
  `hkdfDefaultSalt`.

This is the trusted assumption of this file: that the helper, which calls `Hkdf::<Sha256>` of the
`hkdf` 0.13.0 crate over `Hmac<Sha256>` of `hmac` 0.13.0 and `sha2` 0.11.0, agrees with the
RFC 5869 definitions above for the given `H`. It is a hypothesis of the theorems that use it.
It does not discharge, and is independent of, the assumption that `H` is HMAC-SHA256. Outside
`HkdfSha256Domain` the contract says nothing. There a SHA-256 input of the call can reach 2^61
bytes, and then a build with overflow checks panics inside `sha2` (`Protocols/CONTRACTS.md`,
section 1). Once Extract completes, a buffer longer than 8,160 bytes makes Expand return an error
before it writes any byte, and the contract says nothing about such buffers either. -/
def HkdfSha256RfcContract (H : HmacSha256) : Prop :=
  ∀ (salt : Option (Slice Std.U8)) (ikm info out : Slice Std.U8),
    out.length ≤ 255 * hashLen →
    HkdfSha256Domain (salt.map (·.val)) ikm.val info.val →
    _root_.crypto.hkdf_sha256 salt ikm info out ⦃ r out' =>
      r = .Ok () ∧ out'.length = out.length ∧
        out'.val = hkdfSha256Okm H (salt.map (·.val)) ikm.val info.val out.length ⦄

/-- The 96-byte contract follows from the general one: `HkdfSha256Contract H` is the case of
`HkdfSha256RfcContract H` with an absent salt and a 96-byte buffer. -/
theorem hkdfSha256Contract_of_rfc {H : HmacSha256} (h : HkdfSha256RfcContract H) :
    HkdfSha256Contract H := by
  intro ikm info out h96 h_dom
  have hs := h none ikm info out (by simp [hashLen, h96]) h_dom
  simpa [h96, hkdfSha256Okm_ninetySix] using hs

end libsignal_protocol.crypto
