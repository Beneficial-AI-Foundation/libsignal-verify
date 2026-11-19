/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games

/-!
# IND-CCA Core Hops

Hops 5 and 6 of the PQ security theorem `Protocols.Models.PQXDH.uakeInitiator_secure_pq` in
`Security.lean`: the forgery and indistinguishability cores, against the
KEM's IND-CCA security, the KDF, and the AEAD. See `SecurityLemmas.lean`
for the overall map.

Both hops are stated over original-key partnering (`originalKeyPartnering`). The forgery event
of hop 5 is "Alice accepted and no session of Bob is her original-key partner", and `indistExp`
flips a coin on that event and when a revealed session is a partner.

Unlike the GapDH cores, these reductions are expressible in the current
model: the KDF's PRF key slot is an abstract bitstring (the KEM shared
secret) that the game uses only as a KDF key, so once the IND-CCA hop makes
it uniform, the PRF hypothesis applies directly. The proofs are deferred as
future reduction work.

The lemma statements and proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.Models.PQXDH

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- Hop 5 (forgery core, IND-CCA): with an honest bundle and separated KEM keys, if Alice accepts
  and no session of Bob is her original-key partner, the adversary has broken the KEM, the KDF,
  or the AEAD.

  A session of Bob that completed with a key, holds Alice's associated data and key material
  `(ad, km)`, and accepted no later than Alice is her original-key partner
  (`originalKeyPartnering`). -/
lemma forgeHonestGoodProb_le_pq [SampleableType SS] [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εkem εaead εkdf : ℝ)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      (P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      ((kdfPRF P).prfAdvantage D).toReal ≤ εkdf) :
    forgeHonestGoodProb P msg hasOPK A ≤ q * (εkem + 2 * εaead + εkdf) := by
  sorry

/-- Hop 6 (indistinguishability core, IND-CCA): in `indistExp`, the adversary's guess is better
  than a fair coin only by breaking the KEM or the KDF, or by a KEM public-key collision.

  A partner of Alice holds her associated data and key material, but partnering compares
  `(ad, km)` and not the accepted bundle. Equal key material with a signed pre-key other than the
  one `setup` signed needs degenerate exponents: Alice's identity exponent is `0`, and Bob's
  identity exponent or Alice's ephemeral exponent is `0`. That event has probability about
  `2 / |F| ^ 2` per challenge, and the bound has no term for it.

  Used by `uakeInitiator_secure_pq` as hop 6. -/
lemma indistAdvantage_le_pq [SampleableType SS] [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εkem εkdf εpk : ℝ)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      (P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      ((kdfPRF P).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    indistAdvantage P msg hasOPK A ≤
      q * (εkem + εkdf) + 2 * (q : ℝ) ^ 2 * εpk := by
  sorry

end Protocols.Models.PQXDH
