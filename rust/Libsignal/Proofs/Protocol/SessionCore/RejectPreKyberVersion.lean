/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs

/-! # Spec theorems for `session_core::reject_pre_kyber_version`

The responder's refusal of the pre-Kyber message version. The step rejects a message whose version
is `CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION` (version 3) with an `InvalidMessage` error for a prekey
message and the text "X3DH no longer supported". It lets every other version pass. Rejecting other
versions is not the business of this step: it belongs to the message parser, which this file does
not describe. A comment in the source says that the caller runs this step after it looks for an
existing session, so that an existing session of version 3 is still accepted.

The callers of this step, `process_prekey` and its helpers, are `async` and call the stores of the
application, so the extraction leaves them out. The order of the steps, and of the store calls
between them, is read from `rust/protocol/src/session.rs`. No statement here proves it.

The error branch builds its message with `str::to_owned`, a function outside libsignal. Its
hypothesis names the value of that call and nothing else about it.

**Source**: rust/protocol/src/session_core.rs, lines 166:0-179:1 (`reject_pre_kyber_version`) of the
work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.session_core

/-
natural language description:

• Reads the version of the message. If it is the pre-Kyber version, builds the text "X3DH no longer
  supported" and returns an `InvalidMessage` error for a prekey message. Otherwise returns `Ok`.

natural language specs:

• If the version is the pre-Kyber version, and `to_owned` on the text returns `s`, the call returns
  the error `InvalidMessage PreKey s`.
• If the version is not the pre-Kyber version, the call returns `Ok ()`.
-/

/-- **Spec theorem for `session_core.reject_pre_kyber_version`**, error branch: a message of the
pre-Kyber version is rejected with `InvalidMessage` for a prekey message. `s` is the value of the
call `to_owned`, which is outside libsignal. -/
theorem reject_pre_kyber_version_x3dh (m : protocol.PreKeySignalMessage) (s : String)
    (h : m.message_version = protocol.CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION)
    (hs : Str.Insts.AllocBorrowToOwnedString.to_owned (toStr "X3DH no longer supported") = .ok s) :
    reject_pre_kyber_version m =
      .ok (.Err (error.SignalProtocolError.InvalidMessage
        protocol.CiphertextMessageType.PreKey s)) := by
  sorry

/-- **Spec theorem for `session_core.reject_pre_kyber_version`**, pass branch: a message of any
other version passes. -/
theorem reject_pre_kyber_version_ok (m : protocol.PreKeySignalMessage)
    (h : m.message_version ≠ protocol.CIPHERTEXT_MESSAGE_PRE_KYBER_VERSION) :
    reject_pre_kyber_version m = .ok (.Ok ()) := by
  sorry

end libsignal_protocol.session_core
