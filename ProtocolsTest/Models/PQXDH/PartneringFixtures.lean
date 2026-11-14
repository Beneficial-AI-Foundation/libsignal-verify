/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/

import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games

/-!
# Fixtures for original-key partnering in the PQXDH model

Each fixture builds by hand the end of the challenge stage of one run of the UAKE experiment over
`uakeInitiator`: Alice has accepted, and one session of Bob has accepted and holds his key. The
clock values are those that the oracle's recording rule gives for that run (each message is
recorded at the current clock, which then rises by one), derived by hand. The fixtures evaluate
the experiment's own tests on that end state: `challengePartnered` (the forgery test of the
games), the value of `forgeExp`
(`forgeEvent`, tied to `forgeExp` by `forgeExp_eq_map_forgeEvent`), `revealedPartnered` (the
freshness test of `finalizePartnered`) and the transcript matching `isPingPong` of DF'17.

1. Identifier swap (#35): Bob accepts at tick 4 and Alice at tick 5, but Alice received a bundle
   with other identifiers. Partnered and no forgery, but not matched, so transcript matching
   would count a forgery.
2. Other key material: Bob accepts at tick 4 and Alice at tick 5 on the same messages, but Bob's
   `km` differs from Alice's. Not partnered, and a forgery, whatever the keys.
3. Forge then relay: Alice accepts a forged confirmation at tick 3, and Bob accepts the relayed
   initial message at tick 5. Not partnered, not matched, and a forgery. Once Bob's key is
   revealed, the challenge is not fresh: reveal equivalence has no time condition.

The fixtures check the tests on these end states only. They do not show that a run of the
experiment reaches these states, that the contexts come from `initiate` and `accept`, that the
oracle writes these clocks, or, for the identifier swap, that only identifiers change. Witnesses
that runs reach these states are future work.
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace Protocols.Models.PQXDH.PartneringFixtures

noncomputable section

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- Alice's transcript: the bundle at tick 1, her initial message at tick 2, and the confirmation
  that she accepts at tick `tc`. -/
def aliceTr (b : PreKeyBundle G PQPK S IdC IdK) (im : InitialMessage G CT C IdC IdK) (c : C)
    (tc : ℕ) : Transcript (Message G PQPK CT S C IdC IdK) :=
  ⟨[(.bundle b, 1), (.initial im, 2), (.confirmation c, tc)]⟩

/-- Bob's transcript: his bundle at tick 0, the initial message at tick `ti`, and his confirmation
  at tick `ti + 1`, where he accepts. -/
def bobTr (b : PreKeyBundle G PQPK S IdC IdK) (im : InitialMessage G CT C IdC IdK) (c : C)
    (ti : ℕ) : Transcript (Message G PQPK CT S C IdC IdK) :=
  ⟨[(.bundle b, 0), (.initial im, ti), (.confirmation c, ti + 1)]⟩

/-- The environment at the end of the challenge stage: Alice has accepted with context `ca` and
  transcript `trA`, and Bob's one session has accepted with context `cb` and transcript `trB` and
  holds its key. -/
def endEnv (ca cb : SessionContext G PQPK Msg K SS)
    (trA trB : Transcript (Message G PQPK CT S C IdC IdK)) (revealed : Bool) :
    Env (uakeInitiator P msg hasOPK) :=
  ⟨6, ⟨Sum.inr (Sum.inr ca), trA⟩, true, [⟨Sum.inr cb, trB, some (some cb.sk), revealed⟩]⟩

/-- The challenge result of that stage, as `challengeSession` builds it. -/
def endResult (ca : SessionContext G PQPK Msg K SS)
    (trA trB : Transcript (Message G PQPK CT S C IdC IdK)) :
    ChallengeResult (uakeInitiator P msg hasOPK) :=
  ⟨some ca.sk, trA, [trB]⟩

/-- The value that `forgeExp` returns on a challenge result and the environment at the end of the
  challenge stage (`forgeExp_eq_map_forgeEvent`). -/
def forgeEvent (cr : ChallengeResult (uakeInitiator P msg hasOPK))
    (env : Env (uakeInitiator P msg hasOPK)) : Bool :=
  cr.K0.isSome && !challengePartnered P msg hasOPK cr env

omit [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C] [SampleableType K] in
/-- `forgeExp` is `forgeEvent` on the result of the challenge stage, so the fixtures below test the
  event of the forgery game. -/
theorem forgeExp_eq_map_forgeEvent (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    forgeExp P msg hasOPK A =
      (fun r => forgeEvent P msg hasOPK r.1 r.2.2.1) <$> challengePhase P msg hasOPK A := by
  rw [forgeExp, map_eq_bind_pure_comp]
  refine bind_congr fun r => ?_
  obtain ⟨cr, aSt, env, tk⟩ := r
  rfl

omit [SampleableType K] in
/-- The identifier swap of #35: Alice receives a bundle `b'` with other identifiers than Bob's
  bundle `b`, and the associated data and key material stay equal. Bob is her original-key
  partner, so the run is no forgery, but her transcript does not match his. -/
theorem identifierSwap_partnered (ca cb : SessionContext G PQPK Msg K SS)
    (had : ca.ad = cb.ad) (hkm : ca.km = cb.km)
    (b b' : PreKeyBundle G PQPK S IdC IdK) (hb : b ≠ b')
    (im im' : InitialMessage G CT C IdC IdK) (c : C) :
    challengePartnered P msg hasOPK
        (endResult P msg hasOPK ca (aliceTr b' im' c 5) (bobTr b im c 3))
        (endEnv P msg hasOPK ca cb (aliceTr b' im' c 5) (bobTr b im c 3) false) = true ∧
      isPingPong (endResult P msg hasOPK ca (aliceTr b' im' c 5) (bobTr b im c 3)) = false ∧
      forgeEvent P msg hasOPK
        (endResult P msg hasOPK ca (aliceTr b' im' c 5) (bobTr b im c 3))
        (endEnv P msg hasOPK ca cb (aliceTr b' im' c 5) (bobTr b im c 3) false) = false := by
  have hP : challengePartnered P msg hasOPK
      (endResult P msg hasOPK ca (aliceTr b' im' c 5) (bobTr b im c 3))
      (endEnv P msg hasOPK ca cb (aliceTr b' im' c 5) (bobTr b im c 3) false) = true := by
    unfold challengePartnered
    simp only [decide_eq_true_eq]
    refine ⟨_, List.mem_singleton_self _, ⟨cb.sk, rfl⟩, ?_, 5, 4, rfl, rfl, by omega⟩
    exact (originalKeyPartnering_partner_iff P msg hasOPK _ _).2 ⟨ca, cb, rfl, rfl, had, hkm⟩
  refine ⟨hP, ?_, ?_⟩
  · simp [isPingPong, pingPong, endResult, aliceTr, bobTr, Matching, hb]
  · rw [forgeEvent, hP]
    rfl

omit [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C] [SampleableType K] in
/-- Other key material: Bob accepts at tick 4 and Alice at tick 5 on the same messages, but Bob's
  key material differs from Alice's. Bob is not her partner, whatever the keys, and the run is a
  forgery. -/
theorem otherKeyMaterial_not_partnered (ca cb : SessionContext G PQPK Msg K SS)
    (_had : ca.ad = cb.ad) (hkm : ca.km ≠ cb.km)
    (b : PreKeyBundle G PQPK S IdC IdK) (im : InitialMessage G CT C IdC IdK) (c : C) :
    challengePartnered P msg hasOPK
        (endResult P msg hasOPK ca (aliceTr b im c 5) (bobTr b im c 3))
        (endEnv P msg hasOPK ca cb (aliceTr b im c 5) (bobTr b im c 3) false) = false ∧
      forgeEvent P msg hasOPK
        (endResult P msg hasOPK ca (aliceTr b im c 5) (bobTr b im c 3))
        (endEnv P msg hasOPK ca cb (aliceTr b im c 5) (bobTr b im c 3) false) = true := by
  have hP : challengePartnered P msg hasOPK
      (endResult P msg hasOPK ca (aliceTr b im c 5) (bobTr b im c 3))
      (endEnv P msg hasOPK ca cb (aliceTr b im c 5) (bobTr b im c 3) false) = false := by
    unfold challengePartnered
    simp only [decide_eq_false_iff_not]
    rintro ⟨t, ht, -, hpart, -⟩
    simp only [endEnv, List.mem_singleton] at ht
    subst ht
    obtain ⟨ca', cb', ha, hb', -, hk⟩ :=
      (originalKeyPartnering_partner_iff P msg hasOPK _ _).1 hpart
    have h1 : ca = ca' := Sum.inr.inj (Sum.inr.inj ha)
    have h2 : cb = cb' := Sum.inr.inj hb'
    subst h1 h2
    exact hkm hk
  refine ⟨hP, ?_⟩
  rw [forgeEvent, hP]
  rfl

omit [SampleableType K] in
/-- Forge then relay: Alice accepts a forged confirmation `c'` at tick 3, and Bob accepts the
  relayed initial message at tick 5, sends his confirmation `c`, and holds Alice's associated data
  and key material. Bob accepted after Alice, so he is not her partner, her transcript does not
  match his, and the run is a forgery, whether or not `c'` equals `c`. Once his key is revealed,
  he is reveal-equivalent to her, so the challenge is not fresh. -/
theorem forgeThenRelay_not_partnered (ca cb : SessionContext G PQPK Msg K SS)
    (had : ca.ad = cb.ad) (hkm : ca.km = cb.km)
    (b : PreKeyBundle G PQPK S IdC IdK) (im : InitialMessage G CT C IdC IdK) (c c' : C) :
    challengePartnered P msg hasOPK
        (endResult P msg hasOPK ca (aliceTr b im c' 3) (bobTr b im c 4))
        (endEnv P msg hasOPK ca cb (aliceTr b im c' 3) (bobTr b im c 4) false) = false ∧
      isPingPong (endResult P msg hasOPK ca (aliceTr b im c' 3) (bobTr b im c 4)) = false ∧
      forgeEvent P msg hasOPK
        (endResult P msg hasOPK ca (aliceTr b im c' 3) (bobTr b im c 4))
        (endEnv P msg hasOPK ca cb (aliceTr b im c' 3) (bobTr b im c 4) false) = true ∧
      revealedPartnered (originalKeyPartnering P msg hasOPK)
        (endEnv P msg hasOPK ca cb (aliceTr b im c' 3) (bobTr b im c 4) true).challenge.state
        (endEnv P msg hasOPK ca cb (aliceTr b im c' 3) (bobTr b im c 4) true).tSessions := by
  have hP : challengePartnered P msg hasOPK
      (endResult P msg hasOPK ca (aliceTr b im c' 3) (bobTr b im c 4))
      (endEnv P msg hasOPK ca cb (aliceTr b im c' 3) (bobTr b im c 4) false) = false := by
    unfold challengePartnered
    simp only [decide_eq_false_iff_not]
    rintro ⟨t, ht, -, -, tc, ti, h1, h2, hle⟩
    simp only [endEnv, List.mem_singleton] at ht
    subst ht
    simp [acceptTime, endResult, aliceTr, bobTr] at h1 h2
    omega
  refine ⟨hP, ?_, ?_, ?_⟩
  · simp [isPingPong, pingPong, endResult, aliceTr, bobTr, Matching, interleave, uakeInitiator]
  · rw [forgeEvent, hP]
    rfl
  · exact ⟨_, List.mem_singleton_self _, rfl,
      (originalKeyPartnering_partner_iff P msg hasOPK _ _).2 ⟨ca, cb, rfl, rfl, had, hkm⟩⟩

end

end Protocols.Models.PQXDH.PartneringFixtures
