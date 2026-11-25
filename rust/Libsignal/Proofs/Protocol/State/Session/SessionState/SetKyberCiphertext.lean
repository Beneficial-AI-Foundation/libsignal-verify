/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs

/-! # Spec theorem for `SessionState::set_kyber_ciphertext`

The setter stores pending prekey data in the session of the initiator. `set_kyber_ciphertext` sets
the pending Kyber prekey record: the placeholder ID `u32::MAX`, which a later call replaces by the
ID of the Kyber prekey in the bundle, and the bytes of the Kyber ciphertext. The setter changes
nothing else in the session.

**Source**: rust/protocol/src/state/session.rs, lines 557:4-563:5
(`SessionState::set_kyber_ciphertext`) of the work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.state.session.SessionState

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
  simp [state.session.SessionState.set_kyber_ciphertext]

end libsignal_protocol.state.session.SessionState
