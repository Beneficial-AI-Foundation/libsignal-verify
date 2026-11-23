/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.Funs

/-! # Spec theorem for `pqxdh::pqxdh_initiate`: the call does not read `self_session`

`InitiatorParameters` has a flag `self_session`. `pqxdh_initiate` reads the other fields of the
record and never this flag. So a record that differs from another only in the flag gives the same
result, together with the same state of the random-number generator.
`pqxdh_initiate_self_session` states this for a change of the flag to `false`.

**Source**: rust/protocol/src/pqxdh.rs, lines 201:0-247:1 (`pqxdh_initiate`) of the work copy that
Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.pqxdh

/-
natural language description:

• Reads the key pairs and public keys of the parameter record, computes the Diffie-Hellman secrets,
  encapsulates to the Kyber prekey, and derives the handshake keys. It never reads the field
  `self_session`.

natural language specs:

• For every parameter record, flag and random-number generator state, the call on the record with
  the flag set to `b` is the call on the record with the flag set to `false`.
-/

/-- **Spec theorem for `pqxdh.pqxdh_initiate`**: the result of `pqxdh_initiate` does not depend on
the field `self_session` of the parameters. -/
theorem pqxdh_initiate_self_session {R : Type _} (rng : rand_1.rng.Rng R)
    (crng : rand_core_1.CryptoRng R) (ip : InitiatorParameters) (b : Bool) (r : R) :
    pqxdh_initiate rng crng { ip with self_session := b } r =
      pqxdh_initiate rng crng { ip with self_session := false } r := by
  rfl

end libsignal_protocol.pqxdh
