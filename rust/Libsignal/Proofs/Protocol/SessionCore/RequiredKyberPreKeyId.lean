/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs

/-! # Spec theorems for `session_core::required_kyber_pre_key_id`

The Kyber prekey ID that the message must name. A `PreKeySignalMessage` holds an optional Kyber
payload with an ID and a ciphertext. If the payload is present, the step returns its ID. If it is
absent, the step returns an `InvalidMessage` error for a prekey message with the text
"missing pq pre-key ID".

The ID goes to the store's `get_kyber_pre_key`, which does not tell a one-time key from a
last-resort key. Nothing in this step sees the kind of the key, so the statements cover both kinds.

The callers of this step, `process_prekey` and its helpers, are `async` and call the stores of the
application, so the extraction leaves them out. The order of the steps, and of the store calls
between them, is read from `rust/protocol/src/session.rs`. No statement here proves it.

The error branch builds its message with `str::to_owned`, a function outside libsignal. Its
hypothesis names the value of that call and nothing else about it.

**Source**: rust/protocol/src/session_core.rs, lines 182:0-191:1 (`required_kyber_pre_key_id`) of
the work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.session_core

/-
natural language description:

• Reads the Kyber prekey ID of the message. If there is one, returns it. Otherwise builds the text
  "missing pq pre-key ID" and returns an `InvalidMessage` error for a prekey message.

natural language specs:

• If the Kyber payload of the message is `p`, the call returns `Ok p.pre_key_id`.
• If the message has no Kyber payload, and `to_owned` on the text returns `s`, the call returns the
  error `InvalidMessage PreKey s`.
-/

/-- **Spec theorem for `session_core.required_kyber_pre_key_id`**, present branch: a message with
the Kyber payload `p` gives the ID of `p`. -/
theorem required_kyber_pre_key_id_some (m : protocol.PreKeySignalMessage)
    (p : protocol.KyberPayload) (h : m.kyber_payload = some p) :
    required_kyber_pre_key_id m = .ok (.Ok p.pre_key_id) := by
  sorry

/-- **Spec theorem for `session_core.required_kyber_pre_key_id`**, missing branch: a message with
no Kyber payload is rejected with `InvalidMessage` for a prekey message. `s` is the value of the
call `to_owned`, which is outside libsignal. -/
theorem required_kyber_pre_key_id_none (m : protocol.PreKeySignalMessage) (s : String)
    (h : m.kyber_payload = none)
    (hs : Str.Insts.AllocBorrowToOwnedString.to_owned (toStr "missing pq pre-key ID") = .ok s) :
    required_kyber_pre_key_id m =
      .ok (.Err (error.SignalProtocolError.InvalidMessage
        protocol.CiphertextMessageType.PreKey s)) := by
  sorry

end libsignal_protocol.session_core
