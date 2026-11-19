/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games
import Protocols.ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# GapDH Core Hops

Hops 5 and 6 of the DH security theorem `Protocols.Models.PQXDH.uakeInitiator_secure_dh` in
`Security.lean`: the forgery and indistinguishability cores, against GapDH,
the KDF, and the AEAD. See `SecurityLemmas.lean` for the overall map.

Both hops are stated over original-key partnering (`originalKeyPartnering`). The forgery event
of hop 5 is "Alice accepted and no session of Bob is her original-key partner", and `indistExp`
flips a coin on that event and when a revealed session is a partner.

These statements are believed true in the current model (the KDF as a plain
parameter function, plus a PRF hypothesis), but the standard reductions
require the KDF to be a programmable random oracle, so their proofs are
deferred to that planned model change.

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

/-- Hop 5 (forgery core, GapDH): with an honest bundle and separated KEM keys, if Alice accepts
  and no session of Bob is her original-key partner, the adversary has broken GapDH, the KDF, or
  the AEAD.

  A session of Bob that completed with a key, holds Alice's associated data and key material
  `(ad, km)`, and accepted no later than Alice is her original-key partner
  (`originalKeyPartnering`). A run that changes the key identifiers, a signature on an honestly
  signed key, or the bytes of the one-time pre-key, and leaves `km` unchanged, keeps that partner,
  so it is not in the event. These fields are not authenticated. -/
lemma forgeHonestGoodProb_le_gap [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf : ℝ)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      ((kdfPRFDH P).prfAdvantage D).toReal ≤ εkdf) :
    forgeHonestGoodProb P msg hasOPK A ≤ q * (εgap + 2 * εaead + εkdf) := by
  sorry

/-- Hop 6 (indistinguishability core, GapDH): in `indistExp`, the adversary's guess is better than
  a fair coin only by breaking GapDH, the KDF, or the AEAD, or by a KEM public-key collision.

  A partner of Alice holds her associated data and key material, but partnering compares
  `(ad, km)` and not the accepted bundle. Equal key material with a signed pre-key other than the
  one `setup` signed needs degenerate exponents: Alice's identity exponent is `0`, and Bob's
  identity exponent or Alice's ephemeral exponent is `0`. That event has probability about
  `2 / |F| ^ 2` per challenge, and the bound has no term for it.

  Used by `uakeInitiator_secure_dh` as hop 6. -/
lemma indistAdvantage_le_gap [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf εpk : ℝ)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      ((kdfPRFDH P).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    indistAdvantage P msg hasOPK A ≤
      q * (εgap + εaead + εkdf) + 2 * (q : ℝ) ^ 2 * εpk := by
  sorry

end Protocols.Models.PQXDH
