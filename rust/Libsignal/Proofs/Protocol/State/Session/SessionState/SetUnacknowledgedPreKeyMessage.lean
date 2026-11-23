/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs

/-! # Spec theorems for `SessionState::set_unacknowledged_pre_key_message` and
`SessionState::set_kyber_ciphertext`

The two setters record, in the session of the initiator, what her first message must carry.
`set_unacknowledged_pre_key_message` sets the pending prekey record: the one-time prekey ID, the
signed prekey ID stored as the `i32` wrap of its `u32` value, the bytes of the base key
(`PublicKey::serialize` of the key, copied into a vector), and a time stamp in seconds that the
four clock calls below compute from `now`. `set_kyber_ciphertext` sets the pending Kyber
prekey record: the placeholder ID `u32::MAX`, which a later call replaces by the actual ID, and
the bytes of the Kyber ciphertext. Each setter changes nothing else in the session.

The four calls that read the clock (`SystemTime::UNIX_EPOCH`, `SystemTime::duration_since`,
`Result::unwrap_or_default` and `Duration::as_secs`) are outside libsignal. The hypotheses of
`set_unacknowledged_pre_key_message_eq` name their values and nothing else about them. The call
of `PublicKey::serialize` has a body in libsignal. The equation keeps the call and says nothing
about the bytes that it returns.

**Source**: rust/protocol/src/state/session.rs, lines 537:4-555:5
(`SessionState::set_unacknowledged_pre_key_message`) and 557:4-563:5
(`SessionState::set_kyber_ciphertext`) of the work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.state.session.SessionState

/-
natural language description:

• `set_unacknowledged_pre_key_message`: converts the IDs, serializes the base key and copies the
  bytes into a vector, computes the time stamp from the clock, and stores the pending prekey record
  in the session.

natural language specs:

• If the four clock calls return `e`, `d`, `d'` and `t` as the hypotheses say, the call serializes
  the base key and returns the session with the pending prekey record made of the one-time prekey
  ID, the signed prekey ID wrapped to `i32`, the serialized bytes as a vector, and the time stamp
  `t`.
-/

/-- **Spec theorem for `SessionState.set_unacknowledged_pre_key_message`**. The hypotheses `he`,
`hd`, `hd'` and `ht` name the values of the four clock calls, which are outside libsignal. The
call of `PublicKey.serialize`, which has a body in libsignal, stays in the equation. -/
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
  sorry

/-
natural language description:

• `set_kyber_ciphertext`: converts the slice of ciphertext bytes into a vector and stores the
  pending Kyber prekey record, with the placeholder ID `u32::MAX`, in the session.

natural language specs:

• The call returns the session with the pending Kyber prekey record made of the ID `u32::MAX` and
  the vector of the ciphertext bytes.
-/

/-- **Spec theorem for `SessionState.set_kyber_ciphertext`**: the call returns the session with
the pending Kyber prekey record made of the placeholder ID `u32::MAX` and the bytes of the
ciphertext. -/
theorem set_kyber_ciphertext_eq (st : state.session.SessionState) (ct : Slice Std.U8) :
    st.set_kyber_ciphertext ct =
      .ok { session := { st.session with pending_kyber_pre_key := some (
          { pre_key_id := core.num.U32.MAX, ciphertext := alloc.slice.Slice.into_vec ct } :
            proto.storage.session_structure.PendingKyberPreKey) } } := by
  sorry

end libsignal_protocol.state.session.SessionState
