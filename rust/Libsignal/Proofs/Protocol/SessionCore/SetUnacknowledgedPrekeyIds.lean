/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs

/-! # Spec theorems for `session_core::set_unacknowledged_prekey_ids`

The initiator's pending prekey IDs in `process_prekey_bundle`, which its first message carries.
The step reads the signed prekey ID from the bundle and calls `set_unacknowledged_pre_key_message`
on the session with the one-time prekey ID, that ID, the public key of the base key pair and
`now`. It then reads the Kyber prekey ID from the bundle and calls
`set_unacknowledged_kyber_pre_key_id` on the session that the first call returns, which replaces
the ID of the pending Kyber prekey record. The Rust function takes the session by `&mut`; the
extraction returns the session together with the result of the step.

The two accessors of the bundle return `Ok` on every bundle, so the two error branches of the `?`
operators cannot be reached. The two statements are one equation each, for a received session that
has a pending Kyber prekey record and for one that has none.

The first setter has a body in libsignal. Both equations keep the call, and no hypothesis names the
value of the call. If the call fails, the step fails in the same way. The hypothesis `hp` of each
statement is a fact about the session that the step receives: it has the pending Kyber prekey
record `p`, or it has none. The first setter changes only the pending prekey record, so the second
setter finds in the session that the first one returns what the received session had. With the
record `p`, the right-hand side binds the session that the call returns and replaces the ID of `p`
in it. With no record, the second setter panics, so the step runs the first setter and then
panics; the panic carries no session.

Each printed list of axioms has the three standard ones, the constants that the first setter brings
(the four time operations of `std` and `core` that derive the time stamp, with the types and the
`Default` instance of `Duration` that they use), and two `NonZero` constants of `core`, which the
type of the bundle brings. Neither theorem names any of them in a hypothesis.

**Source**: rust/protocol/src/session_core.rs, lines 115:0-130:1
(`set_unacknowledged_prekey_ids`), and rust/protocol/src/state/bundle.rs, lines 193:4-195:5
(`PreKeyBundle::signed_pre_key_id`) and 209:4-211:5 (`PreKeyBundle::kyber_pre_key_id`), of the
work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.session_core

/-
natural language description:

• Reads the signed prekey ID from the bundle, calls `set_unacknowledged_pre_key_message` on the
  session with the one-time prekey ID, the signed prekey ID, the public key of the base key pair
  and `now`, reads the Kyber prekey ID from the bundle, calls
  `set_unacknowledged_kyber_pre_key_id` on the session that the first call returns, and returns
  `Ok(())` with the session that the second call returns. The second call panics if that session
  has no pending Kyber prekey record.

natural language specs:

• If the session has the pending Kyber prekey record `p`, the step calls
  `set_unacknowledged_pre_key_message` on the session, and returns `Ok(())` with the session that
  this call returns, in which the pending Kyber prekey record is `p` with its ID replaced by the ID
  of the Kyber prekey of the bundle. If the first call fails, the step fails in the same way.
• If the session has no pending Kyber prekey record, the step calls
  `set_unacknowledged_pre_key_message` on the session and then panics. If the first call fails, the
  step fails in the same way.
-/

/-- **Spec theorem for `session_core.set_unacknowledged_prekey_ids`**: for a session with the
pending Kyber prekey record `p`, the step returns `Ok(())` with the session that
`SessionState.set_unacknowledged_pre_key_message` returns, with `p` carrying the ID of the Kyber
prekey of the bundle as the pending Kyber prekey record. The call of the first setter, which has a
body in libsignal, stays in the equation. -/
theorem set_unacknowledged_prekey_ids_eq (st : state.session.SessionState)
    (opkId : Option state.prekey.PreKeyId) (B : state.bundle.PreKeyBundle)
    (kp : libsignal_core.curve.KeyPair) (now : std.time.SystemTime)
    (p : proto.storage.session_structure.PendingKyberPreKey)
    (hp : st.session.pending_kyber_pre_key = some p) :
    set_unacknowledged_prekey_ids st opkId B kp now = (do
      let st₁ ← st.set_unacknowledged_pre_key_message opkId B.ec_signed_pre_key.id
        kp.public_key now
      .ok (.Ok (), { session := { st₁.session with
        pending_kyber_pre_key := some { p with pre_key_id := B.kyber_pre_key.id } } })) := by
  unfold set_unacknowledged_prekey_ids
  simp [state.bundle.PreKeyBundle.signed_pre_key_id, state.bundle.PreKeyBundle.kyber_pre_key_id,
    core.result.Result.Insts.CoreOpsTry.branch,
    state.session.SessionState.set_unacknowledged_pre_key_message,
    state.session.SessionState.set_unacknowledged_kyber_pre_key_id, hp,
    core.option.Option.take, core.option.Option.expect, Result.ofOption,
    core.convert.IntoFrom.into, U32.Insts.CoreConvertFromKyberPreKeyId.from]

/-- **Spec theorem for `session_core.set_unacknowledged_prekey_ids`**, missing branch: for a
session with no pending Kyber prekey record, the step calls
`SessionState.set_unacknowledged_pre_key_message` on it and then panics. The call of the first
setter, which has a body in libsignal, stays in the equation. -/
theorem set_unacknowledged_prekey_ids_none (st : state.session.SessionState)
    (opkId : Option state.prekey.PreKeyId) (B : state.bundle.PreKeyBundle)
    (kp : libsignal_core.curve.KeyPair) (now : std.time.SystemTime)
    (hp : st.session.pending_kyber_pre_key = none) :
    set_unacknowledged_prekey_ids st opkId B kp now = (do
      let _ ← st.set_unacknowledged_pre_key_message opkId B.ec_signed_pre_key.id
        kp.public_key now
      .fail .panic) := by
  unfold set_unacknowledged_prekey_ids
  simp [state.bundle.PreKeyBundle.signed_pre_key_id, state.bundle.PreKeyBundle.kyber_pre_key_id,
    core.result.Result.Insts.CoreOpsTry.branch,
    state.session.SessionState.set_unacknowledged_pre_key_message,
    state.session.SessionState.set_unacknowledged_kyber_pre_key_id, hp,
    core.option.Option.take, core.option.Option.expect, Result.ofOption]

end libsignal_protocol.session_core
