/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs

/-! # Spec theorems for `SessionState::set_unacknowledged_kyber_pre_key_id`

The setter replaces the ID of the pending Kyber prekey of a session. The pending Kyber prekey is
the record that `set_kyber_ciphertext` fills with the ciphertext and the placeholder ID
`u32::MAX`. The setter takes the record out of the session, which panics if there is none, and
puts it back with the new ID. The ID types of the extraction are `u32`, so the conversion of the
ID into `u32` returns the ID itself.

**Source**: rust/protocol/src/state/session.rs, lines 565:4-576:5
(`SessionState::set_unacknowledged_kyber_pre_key_id`) of the work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.state.session.SessionState

/-
natural language description:

• Takes the pending Kyber prekey out of the session, panicking if there is none, sets its ID to
  the given ID, and stores it back. No other field of the session changes.

natural language specs:

• If the session has the pending Kyber prekey `p`, the call returns the session with the pending
  Kyber prekey `p` with its ID replaced by the given ID.
• If the session has no pending Kyber prekey, the call panics.
-/

/-- **Spec theorem for `SessionState.set_unacknowledged_kyber_pre_key_id`**, present branch: the
session with the pending Kyber prekey `p` returns with `p` carrying the new ID. -/
theorem set_unacknowledged_kyber_pre_key_id_some (st : state.session.SessionState)
    (p : proto.storage.session_structure.PendingKyberPreKey)
    (kid : state.kyber_prekey.KyberPreKeyId)
    (h : st.session.pending_kyber_pre_key = some p) :
    st.set_unacknowledged_kyber_pre_key_id kid =
      .ok { session := { st.session with
        pending_kyber_pre_key := some { p with pre_key_id := kid } } } := by
  simp [state.session.SessionState.set_unacknowledged_kyber_pre_key_id, h,
    core.option.Option.take, core.option.Option.expect, Result.ofOption,
    core.convert.IntoFrom.into,
    U32.Insts.CoreConvertFromKyberPreKeyId.from]

/-- **Spec theorem for `SessionState.set_unacknowledged_kyber_pre_key_id`**, missing branch: a
session with no pending Kyber prekey makes the call panic. -/
theorem set_unacknowledged_kyber_pre_key_id_none (st : state.session.SessionState)
    (kid : state.kyber_prekey.KyberPreKeyId)
    (h : st.session.pending_kyber_pre_key = none) :
    st.set_unacknowledged_kyber_pre_key_id kid = .fail .panic := by
  simp [state.session.SessionState.set_unacknowledged_kyber_pre_key_id, h,
    core.option.Option.take, core.option.Option.expect, Result.ofOption]

end libsignal_protocol.state.session.SessionState
