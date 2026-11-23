/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Protocol.SessionCore.RejectPreKyberVersion
import Libsignal.Proofs.Protocol.SessionCore.RequiredKyberPreKeyId
import Libsignal.Proofs.Protocol.SessionCore.SetUnacknowledgedPrekeyIds

/-!
# Spec summary: `rust/protocol/src/session_core.rs`

This file freezes the specifications of the items of `rust/protocol/src/session_core.rs`. Each
theorem is restated with `recall` and has a `#guard_msgs` check on the axioms it depends on.
-/

/-! ## `set_unacknowledged_prekey_ids` -/

open Aeneas Aeneas.Std Result libsignal_protocol libsignal_protocol.session_core in
recall libsignal_protocol.session_core.set_unacknowledged_prekey_ids_eq
    (st : state.session.SessionState)
    (opkId : Option state.prekey.PreKeyId) (B : state.bundle.PreKeyBundle)
    (kp : libsignal_core.curve.KeyPair) (now : std.time.SystemTime)
    (p : proto.storage.session_structure.PendingKyberPreKey)
    (hp : st.session.pending_kyber_pre_key = some p) :
    set_unacknowledged_prekey_ids st opkId B kp now = (do
      let st₁ ← st.set_unacknowledged_pre_key_message opkId B.ec_signed_pre_key.id
        kp.public_key now
      .ok (.Ok (), { session := { st₁.session with
        pending_kyber_pre_key := some { p with pre_key_id := B.kyber_pre_key.id } } }))

/--
info: 'libsignal_protocol.session_core.set_unacknowledged_prekey_ids_eq' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 core.time.Duration,
 std.time.SystemTime,
 std.time.SystemTimeError,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 core.result.Result.unwrap_or_default,
 core.time.Duration.as_secs,
 std.time.SystemTime.UNIX_EPOCH,
 std.time.SystemTime.duration_since,
 core.time.Duration.Insts.CoreDefaultDefault.default]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.session_core.set_unacknowledged_prekey_ids_eq

/-! ## `reject_pre_kyber_version` -/

open Aeneas Aeneas.Std Result libsignal_protocol libsignal_protocol.session_core in
recall libsignal_protocol.session_core.reject_pre_kyber_version_x3dh
    (m : protocol.PreKeySignalMessage) (s : String)
    (h : m.message_version = protocol.CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION)
    (hs : Str.Insts.AllocBorrowToOwnedString.to_owned (toStr "X3DH no longer supported") = .ok s) :
    reject_pre_kyber_version m =
      .ok (.Err (error.SignalProtocolError.InvalidMessage protocol.CiphertextMessageType.PreKey s))

/--
info: 'libsignal_protocol.session_core.reject_pre_kyber_version_x3dh' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.session_core.reject_pre_kyber_version_x3dh

open Aeneas Aeneas.Std Result libsignal_protocol libsignal_protocol.session_core in
recall libsignal_protocol.session_core.reject_pre_kyber_version_ok
    (m : protocol.PreKeySignalMessage)
    (h : m.message_version ≠ protocol.CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION) :
    reject_pre_kyber_version m = .ok (.Ok ())

/--
info: 'libsignal_protocol.session_core.reject_pre_kyber_version_ok' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.session_core.reject_pre_kyber_version_ok

/-! ## `required_kyber_pre_key_id` -/

open Aeneas Aeneas.Std Result libsignal_protocol libsignal_protocol.session_core in
recall libsignal_protocol.session_core.required_kyber_pre_key_id_some
    (m : protocol.PreKeySignalMessage)
    (p : protocol.KyberPayload) (h : m.kyber_payload = some p) :
    required_kyber_pre_key_id m = .ok (.Ok p.pre_key_id)

/--
info: 'libsignal_protocol.session_core.required_kyber_pre_key_id_some' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.session_core.required_kyber_pre_key_id_some

open Aeneas Aeneas.Std Result libsignal_protocol libsignal_protocol.session_core in
recall libsignal_protocol.session_core.required_kyber_pre_key_id_none
    (m : protocol.PreKeySignalMessage) (s : String)
    (h : m.kyber_payload = none)
    (hs : Str.Insts.AllocBorrowToOwnedString.to_owned (toStr "missing pq pre-key ID") = .ok s) :
    required_kyber_pre_key_id m =
      .ok (.Err (error.SignalProtocolError.InvalidMessage
        protocol.CiphertextMessageType.PreKey s))

/--
info: 'libsignal_protocol.session_core.required_kyber_pre_key_id_none' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.session_core.required_kyber_pre_key_id_none
