/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.Models.PQXDH

/-!
# Spec summary: the abstract PQXDH model

This file freezes the headline theorems of the abstract model in `Protocols/Models/PQXDH/`: the
six endpoint theorems and the six security hops that the two security theorems use. Each theorem
is restated with `recall` and has a `#guard_msgs` check on the axioms it depends on.

The stub marker in the closures of the two security theorems comes from the admitted hops listed
in `Protocols/LEDGER.md`. The docstrings and module notes in `Protocols/Models/PQXDH/UAKE/` state
the scope of each theorem and of its premises.
-/

/-! ## Correctness -/

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
recall Protocols.Models.PQXDH.uakeInitiator_perfectlyCorrect
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) ProbCompRuntime.probComp

/--
info: 'Protocols.Models.PQXDH.uakeInitiator_perfectlyCorrect' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.uakeInitiator_perfectlyCorrect

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
recall Protocols.Models.PQXDH.uakeRecipient_perfectlyCorrect
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) ProbCompRuntime.probComp

/--
info: 'Protocols.Models.PQXDH.uakeRecipient_perfectlyCorrect' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.uakeRecipient_perfectlyCorrect

/-! ## Well-formedness -/

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
recall Protocols.Models.PQXDH.uakeInitiator_wellFormed
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    (uakeInitiator P msg hasOPK).WellFormed

/--
info: 'Protocols.Models.PQXDH.uakeInitiator_wellFormed' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.uakeInitiator_wellFormed

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
recall Protocols.Models.PQXDH.uakeRecipient_wellFormed
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    (uakeRecipient P msg hasOPK).WellFormed

/--
info: 'Protocols.Models.PQXDH.uakeRecipient_wellFormed' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.uakeRecipient_wellFormed

/-! ## Security -/

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
open scoped ENNReal in
recall Protocols.Models.PQXDH.uakeInitiator_secure_dh
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited F]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq SS] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εgap εaead εkdf εpk : ℝ)
    (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.JointAdversary (DH : F → G → G), B.advantage.toReal ≤ εsig)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      ((kdfPRFDH P).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    UAKE.advantage ProbCompRuntime.probComp A ≤
      εsig + 2 * q * (εgap + 2 * εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk

/--
info: 'Protocols.Models.PQXDH.uakeInitiator_secure_dh' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.uakeInitiator_secure_dh

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
open scoped ENNReal in
recall Protocols.Models.PQXDH.uakeInitiator_secure_pq
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [SampleableType SS] [DecidableEq SS]
    [Inhabited S] [Inhabited F] [Inhabited PQSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf εpk : ℝ)
    (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hsig : ∀ B : P.sig.JointAdversary (DH : F → G → G), B.advantage.toReal ≤ εsig)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      (P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      ((kdfPRF P).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    UAKE.advantage ProbCompRuntime.probComp A ≤
      εsig + 2 * q * (εkem + εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk

/--
info: 'Protocols.Models.PQXDH.uakeInitiator_secure_pq' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.uakeInitiator_secure_pq

/-! ## Security hops

Hops 3 and 4, shared by both security theorems, and hops 5 and 6 for the DH and the PQ theorem.
Hop 4 is proved. `Protocols/LEDGER.md` lists the other five as admitted lemmas. -/

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
recall Protocols.Models.PQXDH.sigForgeProb_le_sig
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq S] [DecidableEq Msg]
    [DecidableEq IdC] [DecidableEq IdK] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    [Inhabited S] [Inhabited F]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (εsig : ℝ)
    (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.JointAdversary (DH : F → G → G), B.advantage.toReal ≤ εsig) :
    sigForgeProb P msg hasOPK A ≤ εsig

/--
info: 'Protocols.Models.PQXDH.sigForgeProb_le_sig' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.sigForgeProb_le_sig

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
open scoped ENNReal in
recall Protocols.Models.PQXDH.pqpkGuessedProb_le
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q) (εpk : ℝ)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    pqpkGuessedProb P msg hasOPK A ≤ (q : ℝ) ^ 2 * εpk

/--
info: 'Protocols.Models.PQXDH.pqpkGuessedProb_le' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.pqpkGuessedProb_le

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
recall Protocols.Models.PQXDH.forgeHonestGoodProb_le_gap
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf : ℝ) (hidKEM : Function.Injective P.idKEM)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      ((kdfPRFDH P).prfAdvantage D).toReal ≤ εkdf) :
    forgeHonestGoodProb P msg hasOPK A ≤ (q : ℝ) * (εgap + 2 * εaead + εkdf)

/--
info: 'Protocols.Models.PQXDH.forgeHonestGoodProb_le_gap' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.forgeHonestGoodProb_le_gap

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
open scoped ENNReal in
recall Protocols.Models.PQXDH.indistAdvantage_le_gap
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf εpk : ℝ) (hidKEM : Function.Injective P.idKEM)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      ((kdfPRFDH P).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    indistAdvantage P msg hasOPK A ≤
      (q : ℝ) * (εgap + εaead + εkdf) + 2 * (q : ℝ) ^ 2 * εpk

/--
info: 'Protocols.Models.PQXDH.indistAdvantage_le_gap' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.indistAdvantage_le_gap

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
recall Protocols.Models.PQXDH.forgeHonestGoodProb_le_pq
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    [SampleableType SS] [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εkem εaead εkdf : ℝ) (hidKEM : Function.Injective P.idKEM)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      (P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      ((kdfPRF P).prfAdvantage D).toReal ≤ εkdf) :
    forgeHonestGoodProb P msg hasOPK A ≤ (q : ℝ) * (εkem + 2 * εaead + εkdf)

/--
info: 'Protocols.Models.PQXDH.forgeHonestGoodProb_le_pq' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.forgeHonestGoodProb_le_pq

open OracleSpec OracleComp AKE AKE.UAKE Protocols.Models.PQXDH in
open scoped ENNReal in
recall Protocols.Models.PQXDH.indistAdvantage_le_pq
    {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    [SampleableType SS] [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εkem εkdf εpk : ℝ) (hidKEM : Function.Injective P.idKEM)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      (P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      ((kdfPRF P).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    indistAdvantage P msg hasOPK A ≤ (q : ℝ) * (εkem + εkdf) + 2 * (q : ℝ) ^ 2 * εpk

/--
info: 'Protocols.Models.PQXDH.indistAdvantage_le_pq' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Models.PQXDH.indistAdvantage_le_pq
