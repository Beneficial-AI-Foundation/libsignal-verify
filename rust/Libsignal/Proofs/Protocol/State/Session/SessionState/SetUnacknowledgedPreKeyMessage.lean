/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs

/-! # Spec theorem for `SessionState::set_unacknowledged_pre_key_message`

The setter stores pending prekey data in the session of the initiator.
`set_unacknowledged_pre_key_message` sets the pending prekey record: the one-time prekey ID, the
signed prekey ID stored as an `i32` with the same 32 bits as its `u32` value, the bytes of the base
key (`PublicKey::serialize` of the key, copied into a vector), and the local creation time of the
record in seconds, which the four time operations below compute from the argument `now`. The
initiator's first message, the prekey message, has no field for this time. The setter changes
nothing else in the session.

The four operations used to derive the time stamp from `now` (`SystemTime::UNIX_EPOCH`,
`SystemTime::duration_since`, `Result::unwrap_or_default` and `Duration::as_secs`) are outside
libsignal. The hypotheses of `set_unacknowledged_pre_key_message_eq` name their values and nothing
else about them. The call of `PublicKey::serialize` has a body in libsignal. The equation keeps the
call and says nothing about the bytes that it returns.

**Source**: rust/protocol/src/state/session.rs, lines 537:4-555:5
(`SessionState::set_unacknowledged_pre_key_message`) of the work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.state.session.SessionState

/-
natural language description:

• `set_unacknowledged_pre_key_message`: converts the IDs, serializes the base key and copies the
  bytes into a vector, computes the time stamp from `now`, and stores the pending prekey record
  in the session.

natural language specs:

• If the four time operations return `e`, `d`, `d'` and `t` as the hypotheses say, the call
  serializes the base key and returns the session with the pending prekey record made of the
  one-time prekey ID, the signed prekey ID wrapped to `i32`, the serialized bytes as a vector, and
  the time stamp `t`.
-/

/-- **Spec theorem for `SessionState.set_unacknowledged_pre_key_message`**: the call returns the
session with the pending prekey record made of the IDs, the serialized base key and the time stamp
`t`. The hypotheses `he`, `hd`, `hd'` and `ht` name the values of the four time operations, which
are outside libsignal. The call of `PublicKey.serialize`, which has a body in libsignal, stays in
the equation. -/
theorem set_unacknowledged_pre_key_message_eq (st : state.session.SessionState)
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
            proto.storage.session_structure.PendingPreKey) } }) := by
  have hv : ∀ s : Slice Std.U8,
      alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok { slice := s } := by
    intro s
    have h := alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (fun _ _ => rfl)
    cases hr : alloc.slice.Slice.to_vec core.clone.CloneU8 s with
    | ret v =>
      rw [hr] at h
      have h' : s = v.slice := (Aeneas.Std.WP.spec_ok v).mp h
      rw [h']
    | vis e k => rw [hr] at h; exact ((Aeneas.Std.WP.spec_vis e k).mp h).elim
    | div => rw [hr] at h; exact (Aeneas.Std.WP.spec_div.mp h).elim
  unfold state.session.SessionState.set_unacknowledged_pre_key_message
  simp [he, hd, hd', ht, hv, core.convert.IntoFrom.into,
    U32.Insts.CoreConvertFromSignedPreKeyId.from, U32.Insts.CoreConvertFromPreKeyId.from,
    core.option.Option.map, P.Insts.CoreOpsFunctionFnOnceTupleTU.call_once]
  cases opk <;> simp [lift]

end libsignal_protocol.state.session.SessionState
