/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs

/-! # Spec theorem for `pqxdh::pqxdh_accept`: the call does not read `self_session`

`RecipientParameters` has a flag `self_session`. `pqxdh_accept` reads the other fields of the
record and never this flag. So a record that differs from another only in the flag gives the same
result. `pqxdh_accept_self_session` states this for a change of the flag to `false`.

**Source**: rust/protocol/src/pqxdh.rs, lines 337:0-387:1 (`pqxdh_accept`) of the work copy that
Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.pqxdh

/-
natural language description:

• Checks that the sender's ephemeral key is canonical, computes the Diffie-Hellman secrets with the
  key pairs of the record, decapsulates the Kyber ciphertext, and derives the handshake keys. It
  never reads the field `self_session`.

natural language specs:

• For every parameter record and flag, the call on the record with the flag set to `b` is the
  call on the record with the flag set to `false`.
-/

/-- **Spec theorem for `pqxdh.pqxdh_accept`**: the result of `pqxdh_accept` does not depend on the
field `self_session` of the parameters. -/
theorem pqxdh_accept_self_session (rp : RecipientParameters) (b : Bool) :
    pqxdh_accept { rp with self_session := b } =
      pqxdh_accept { rp with self_session := false } := by
  sorry

end libsignal_protocol.pqxdh
