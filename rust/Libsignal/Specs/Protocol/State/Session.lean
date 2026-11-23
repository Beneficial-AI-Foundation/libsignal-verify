/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Protocol.State.Session.SessionState.SetUnacknowledgedKyberPreKeyId
import Libsignal.Proofs.Protocol.State.Session.SessionState.SetUnacknowledgedPreKeyMessage

/-!
# Spec summary: `rust/protocol/src/state/session.rs`

This file freezes the specifications of the items of `rust/protocol/src/state/session.rs`. Each
theorem is restated with `recall` and has a `#guard_msgs` check on the axioms it depends on.
-/

/-! ## `SessionState::set_unacknowledged_pre_key_message` -/

open Aeneas Aeneas.Std Result libsignal_protocol libsignal_protocol.state.session.SessionState in
recall libsignal_protocol.state.session.SessionState.set_unacknowledged_pre_key_message_eq
    (st : state.session.SessionState)
    (opk : Option state.prekey.PreKeyId) (spkId : state.signed_prekey.SignedPreKeyId)
    (base : libsignal_core.curve.PublicKey) (now e : std.time.SystemTime)
    (d : core.result.Result core.time.Duration std.time.SystemTimeError)
    (d' : core.time.Duration) (t : Std.U64)
    (he : std.time.SystemTime.UNIX_EPOCH = .ok e)
    (hd : std.time.SystemTime.duration_since now e = .ok d)
    (hd' : core.result.Result.unwrap_or_default
      core.time.Duration.Insts.CoreDefaultDefault d = .ok d')
    (ht : core.time.Duration.as_secs d' = .ok t) :
    st.set_unacknowledged_pre_key_message opk spkId base now = (do
      let s ← libsignal_core.curve.PublicKey.serialize base
      .ok { session := { st.session with pending_pre_key := some (
          { pre_key_id := opk, signed_pre_key_id := UScalar.hcast .I32 spkId,
            base_key := { slice := s }, timestamp := t } :
            proto.storage.session_structure.PendingPreKey) } })

/--
info: 'libsignal_protocol.state.session.SessionState.set_unacknowledged_pre_key_message_eq'
 depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 core.time.Duration,
 std.time.SystemTime,
 std.time.SystemTimeError,
 core.result.Result.unwrap_or_default,
 core.time.Duration.as_secs,
 std.time.SystemTime.UNIX_EPOCH,
 std.time.SystemTime.duration_since,
 core.time.Duration.Insts.CoreDefaultDefault.default]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.state.session.SessionState.set_unacknowledged_pre_key_message_eq

/-! ## `SessionState::set_kyber_ciphertext` -/

open Aeneas Aeneas.Std Result libsignal_protocol libsignal_protocol.state.session.SessionState in
recall libsignal_protocol.state.session.SessionState.set_kyber_ciphertext_eq
    (st : state.session.SessionState) (ct : Slice Std.U8) :
    st.set_kyber_ciphertext ct =
      .ok { session := { st.session with pending_kyber_pre_key := some (
          { pre_key_id := core.num.U32.MAX, ciphertext := alloc.slice.Slice.into_vec ct } :
            proto.storage.session_structure.PendingKyberPreKey) } }

/--
info: 'libsignal_protocol.state.session.SessionState.set_kyber_ciphertext_eq' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.state.session.SessionState.set_kyber_ciphertext_eq

/-! ## `SessionState::set_unacknowledged_kyber_pre_key_id` -/

open Aeneas Aeneas.Std Result libsignal_protocol libsignal_protocol.state.session.SessionState in
recall libsignal_protocol.state.session.SessionState.set_unacknowledged_kyber_pre_key_id_some
    (st : state.session.SessionState)
    (p : proto.storage.session_structure.PendingKyberPreKey)
    (kid : state.kyber_prekey.KyberPreKeyId)
    (h : st.session.pending_kyber_pre_key = some p) :
    st.set_unacknowledged_kyber_pre_key_id kid =
      .ok { session := { st.session with
        pending_kyber_pre_key := some { p with pre_key_id := kid } } }

/--
info: 'libsignal_protocol.state.session.SessionState.set_unacknowledged_kyber_pre_key_id_some'
 depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.state.session.SessionState.set_unacknowledged_kyber_pre_key_id_some

open Aeneas Aeneas.Std Result libsignal_protocol libsignal_protocol.state.session.SessionState in
recall libsignal_protocol.state.session.SessionState.set_unacknowledged_kyber_pre_key_id_none
    (st : state.session.SessionState)
    (kid : state.kyber_prekey.KyberPreKeyId)
    (h : st.session.pending_kyber_pre_key = none) :
    st.set_unacknowledged_kyber_pre_key_id kid = .fail .panic

/--
info: 'libsignal_protocol.state.session.SessionState.set_unacknowledged_kyber_pre_key_id_none'
 depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.state.session.SessionState.set_unacknowledged_kyber_pre_key_id_none
