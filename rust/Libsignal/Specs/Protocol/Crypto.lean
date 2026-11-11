/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Protocol.Crypto.HkdfSha256

/-!
# Spec summary: `rust/protocol/src/crypto.rs`

This file freezes the specification of `crypto::hkdf_sha256` from `rust/protocol/src/crypto.rs`:
the RFC 5869 definitions computed from an assumed MAC interface, the contract that the opaque
extracted function meets them, and the lemmas about both. Each theorem is restated with `recall`
and has a `#guard_msgs` check on the axioms it depends on. A definition has the axiom check only.
-/

/-! ## Lemmas -/

open Aeneas Aeneas.Std libsignal_protocol.crypto in
recall libsignal_protocol.crypto.hkdfExpand96_length (H : HmacSha256) (prk info : List Std.U8) :
    (hkdfExpand96 H prk info).length = 96

/--
info: 'libsignal_protocol.crypto.hkdfExpand96_length' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.hkdfExpand96_length

open Aeneas Aeneas.Std Result libsignal_protocol.crypto in
recall libsignal_protocol.crypto.hkdf_sha256_okm96_spec {H : HmacSha256}
    (h : HkdfSha256Contract H) (ikm info out : Slice Std.U8) (h_len : out.length = 96) :
    crypto.hkdf_sha256 none ikm info out ⦃ r out' =>
      r = .Ok () ∧ out'.length = out.length ∧
        out'.val = hkdfSha256Okm96 H none ikm.val info.val ⦄

/--
info: 'libsignal_protocol.crypto.hkdf_sha256_okm96_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.hkdf_sha256_okm96_spec

/-! ## Definitions -/

/-- info: 'libsignal_protocol.crypto.HmacSha256' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.HmacSha256

/-- info: 'libsignal_protocol.crypto.hashLen' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.hashLen

/--
info: 'libsignal_protocol.crypto.hkdfDefaultSalt' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.hkdfDefaultSalt

/--
info: 'libsignal_protocol.crypto.hkdfExtract' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.hkdfExtract

/-- info: 'libsignal_protocol.crypto.hkdfExpandBlock' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.hkdfExpandBlock

/--
info: 'libsignal_protocol.crypto.hkdfExpand96' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.hkdfExpand96

/--
info: 'libsignal_protocol.crypto.hkdfSha256Okm96' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.hkdfSha256Okm96

/--
info: 'libsignal_protocol.crypto.HkdfSha256Contract' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.crypto.HkdfSha256Contract
