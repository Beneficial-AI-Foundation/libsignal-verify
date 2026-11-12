/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Protocol.Pqxdh.HandshakeKeys.Derive

/-!
# Spec summary: `rust/protocol/src/pqxdh.rs`

This file freezes the specifications of the items of `rust/protocol/src/pqxdh.rs`. Each theorem
is restated with `recall` and has a `#guard_msgs` check on the axioms it depends on. A
definition, including the two extracted entry points, has only the axiom check.

The closures of `pqxdh_initiate` and `pqxdh_accept` list the logical axioms of Lean, the opaque
primitives and backend items of the extraction that the two functions call, and the
native-decision constant that the extraction of `pqxdh_accept` introduces.
-/

/-! ## `HandshakeKeys::derive_with_label` and `HandshakeKeys::derive` -/

open Aeneas Aeneas.Std Result libsignal_protocol.crypto libsignal_protocol.pqxdh in
recall libsignal_protocol.pqxdh.HandshakeKeys.derive_with_label_spec (H : HmacSha256)
    (h_hkdf : HkdfSha256Contract H) (label secret_input : Slice Std.U8) :
    HandshakeKeys.derive_with_label label secret_input ⦃ (keys : HandshakeKeys) =>
      let okm := hkdfSha256Okm96 H none secret_input.val label.val
      (keys.root_key.key).val = okm.slice 0 32 ∧
      (keys.chain_key.key).val = okm.slice 32 64 ∧
      keys.chain_key.index = 0#u32 ∧
      keys.pqr_key.val = okm.slice 64 96 ⦄

/--
info: 'libsignal_protocol.pqxdh.HandshakeKeys.derive_with_label_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.pqxdh.HandshakeKeys.derive_with_label_spec

open libsignal_protocol.pqxdh in
recall libsignal_protocol.pqxdh.HandshakeKeys.pqxdhKdfLabel_eq_utf8 :
    HandshakeKeys.pqxdhKdfLabel.map (·.val) =
      ("WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8.toList.map (·.toNat))

/--
info: 'libsignal_protocol.pqxdh.HandshakeKeys.pqxdhKdfLabel_eq_utf8' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.pqxdh.HandshakeKeys.pqxdhKdfLabel_eq_utf8

open Aeneas Aeneas.Std Result libsignal_protocol.crypto libsignal_protocol.pqxdh in
recall libsignal_protocol.pqxdh.HandshakeKeys.derive_spec (H : HmacSha256)
    (h_hkdf : HkdfSha256Contract H) (secret_input : Slice Std.U8) :
    HandshakeKeys.derive secret_input ⦃ (keys : HandshakeKeys) =>
      let okm := hkdfSha256Okm96 H none secret_input.val HandshakeKeys.pqxdhKdfLabel
      (keys.root_key.key).val = okm.slice 0 32 ∧
      (keys.chain_key.key).val = okm.slice 32 64 ∧
      keys.chain_key.index = 0#u32 ∧
      keys.pqr_key.val = okm.slice 64 96 ⦄

/--
info: 'libsignal_protocol.pqxdh.HandshakeKeys.derive_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.pqxdh.HandshakeKeys.derive_spec

/-! ## Definitions -/

/--
info: 'libsignal_protocol.pqxdh.HandshakeKeys.pqxdhKdfLabel' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.pqxdh.HandshakeKeys.pqxdhKdfLabel

/--
info: 'libsignal_protocol.pqxdh.pqxdh_initiate' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.pqxdh.pqxdh_initiate

/--
info: 'libsignal_protocol.pqxdh.pqxdh_accept' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PublicKey.is_torsion_free,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.pqxdh.pqxdh_accept
