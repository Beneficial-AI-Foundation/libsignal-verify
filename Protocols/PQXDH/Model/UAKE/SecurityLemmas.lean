/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.SecurityLemmas.Games
import Protocols.PQXDH.Model.UAKE.SecurityLemmas.SharedHops
import Protocols.PQXDH.Model.UAKE.SecurityLemmas.DHHops
import Protocols.PQXDH.Model.UAKE.SecurityLemmas.PQHops

/-!
# Security Lemmas for the PQXDH model

Game hops scaffolding the proofs of the top-level security theorems
`Protocols.PQXDH.uakeInitiator_secure_dh` and `Protocols.PQXDH.uakeInitiator_secure_pq` in
`Security.lean`. Both proofs split the UAKE experiment into a forgery
branch (the challenge session completes on a transcript that matches no
T-oracle session) and an indistinguishability branch (the adversary
distinguishes the accepted session key from random). They share Hops 1
through 4 and differ only in the core hops, which bound the two branches
against GapDH (the DH theorem) or the KEM's IND-CCA security (the PQ
theorem):

* Hop 1 (`advantage_le_forgeProb_add_indistAdvantage`, `SharedHops.lean`):
  replace the outright win awarded for a forgery with a fair coin flip; the
  UAKE advantage is bounded by the forgery probability plus the modified
  experiment's advantage.
* Hop 2 (`forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood`,
  `SharedHops.lean`): a forgery is a signature forgery, a KEM public-key
  collision or prediction, or a forgery on an honestly signed bundle with
  separated KEM keys.
* Hop 3 (`sigForgeProb_le_sig`, `SharedHops.lean`): the SUF-CMA reduction
  for dishonest bundles.
* Hop 4 (`pqpkGuessedProb_le`, `SharedHops.lean`): KEM public-key
  collisions and predictions reduce to guessing the public key output by
  `P.pqkem.keygen`.
* Hop 5 (`forgeHonestGoodProb_le_gap` in `DHHops.lean`,
  `forgeHonestGoodProb_le_pq` in `PQHops.lean`): the forgery cores.
* Hop 6 (`indistAdvantage_le_gap` in `DHHops.lean`,
  `indistAdvantage_le_pq` in `PQHops.lean`): the indistinguishability
  cores.

The games and event predicates live in `SecurityLemmas/Games.lean`. Hops 1
and 2 are proven; they are purely probabilistic. Hops 3 and 4 are deferred
as reduction work, with the intended reductions recorded in their doc
comments. The GapDH cores idealize the KDF outputs on the challenge
session's key material, which requires the KDF to be a programmable random
oracle, so their proofs are deferred to that planned model change. The IND-CCA cores
are expressible in the current model (the KDF's PRF key slot is the KEM
shared secret, which the IND-CCA hop makes uniform) and are deferred as
future reduction work. Both forgery cores also face the transcript-binding
gap recorded in their docstrings: the last step of their proof plans infers
matching transcripts from a verbatim relay, but unsigned bundle fields can
change without changing the derived keys. The well-formedness lemmas in
`WellFormedLemmas.lean` (parties output exactly at completion, honest runs
transfer exactly `rounds` messages) are expected to discharge the
bookkeeping relating `K0` to challenge-session completion.

The contents of this file and the `SecurityLemmas/` directory are
AI-written.
-/
