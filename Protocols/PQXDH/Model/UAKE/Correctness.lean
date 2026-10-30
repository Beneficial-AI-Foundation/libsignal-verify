/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.CorrectnessLemmas

/-!
# Top-level Correctness Theorems for the PQXDH model
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

/-- The PQXDH model in the T=Bob direction has perfect UAKE correctness,
  assuming the KEM and AEAD are perfectly correct and the signature is
  perfectly complete (i.e., never fails on an honestly generated signature,
  when paired with the message used to generate it).

  The conclusion `UAKE.PerfectlyCorrect` also holds for a scheme whose parties
  always reject (see `UAKE.CorrectExp`), so the statement alone does not
  establish honest completion. The proof does derive that both parties output
  the same key, through `run_support_initiator`, but the statement does not
  record it. The statement is the paper's Def. 7 for the abstract model. It is
  not correctness of production PQXDH, and `hkem` assumes perfect KEM
  correctness, which production Kyber does not have. -/
theorem uakeInitiator_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) ProbCompRuntime.probComp := by
  unfold UAKE.PerfectlyCorrect
  rw [probOutput_probComp_evalDist]
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeInitiator, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, ms, hrun, rfl⟩ := hb
  suffices h : ∃ k, uOut = some (some k) ∧ tOut = some (some k) by
    obtain ⟨k, rfl, rfl⟩ := h
    simp
  simp only [setup, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsetup
  obtain ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB,
    huk, htk⟩ := hsetup
  subst huk htk
  exact (run_support_initiator P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB
    hspkSigB hrun).1

/-- The PQXDH model in the T=Alice direction has perfect UAKE correctness,
  assuming the KEM and AEAD are perfectly correct and the signature is
  perfectly complete (i.e., never fails on an honestly generated signature,
  when paired with the message used to generate it).

  Correctness only: `uakeRecipient` has no advantage statement and no
  partnering.

  The conclusion `UAKE.PerfectlyCorrect` also holds for a scheme whose parties
  always reject (see `UAKE.CorrectExp`), so the statement alone does not
  establish honest completion. The proof does derive that both parties output
  the same key, through `run_support_recipient`, but the statement does not
  record it. The statement is the paper's Def. 7 for the abstract model. It is
  not correctness of production PQXDH, and `hkem` assumes perfect KEM
  correctness, which production Kyber does not have. -/
theorem uakeRecipient_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) ProbCompRuntime.probComp := by
  unfold UAKE.PerfectlyCorrect
  rw [probOutput_probComp_evalDist]
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeRecipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, ms, hrun, rfl⟩ := hb
  suffices h : ∃ k, uOut = some (some k) ∧ tOut = some (some k) by
    obtain ⟨k, rfl, rfl⟩ := h
    simp
  simp only [setup, support_map, Set.mem_image, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hsetup
  obtain ⟨x, ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB, rfl⟩,
    hswap⟩ := hsetup
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
  obtain ⟨huk, htk⟩ := hswap
  subst huk htk
  exact (run_support_recipient P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB
    hspkSigB hrun).1

end Protocols.PQXDH
