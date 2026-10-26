/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.CorrectnessLemmas

/-!
# Well-formedness Lemmas for the PQXDH model

Supporting lemmas for `WellFormed.lean`: unconditional
outputs-only-at-completion facts for the four model parties, unconditional
facts that their output functions are pure, and transcript-length
characterizations of honest runs started from `setup`.
The length lemmas are also used by the Aeneas instantiations'
well-formedness proofs. The proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace Protocols.PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

/-- The model initiator outputs a key exactly on the states reached by a
  completed run: `none` on its initial and mid-handshake states, `some` on
  the state installed by a successful `confirm`. -/
lemma initiator_outputsOnlyAtCompletion
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    (initiator P).OutputsOnlyAtCompletion := by
  unfold Party.OutputsOnlyAtCompletion
  refine ⟨?_, ?_, ?_⟩
  · intro i r hr out hout
    obtain rfl := eq_of_mem_support_pure hr
    exact eq_of_mem_support_pure hout
  · intro st w st' hst' out hout
    rcases st with p | ctx | k
    · rcases w with b | im | conf
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ⟨im', ctx⟩ <;>
          exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · rcases hc : confirm P ctx conf with _ | SK <;>
            simp only [initiator, hc] at hst'
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain rfl := Party.StepResult.complete.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)
  · intro st w st' w' done hst' out hout
    rcases st with p | ctx | k
    · rcases w with b | im | conf
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ⟨im', ctx⟩
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain ⟨rfl, -, rfl⟩ :=
            Party.StepResult.acceptAndSend.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · rcases hc : confirm P ctx conf with _ | SK <;>
            simp only [initiator, hc] at hst' <;>
          exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)

/-- The model initiator's output function has no effect: on every state it
  returns a fixed value. -/
lemma initiator_pureOutput
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    (initiator P).PureOutput := by
  rintro (p | ctx | k) <;> exact ⟨_, rfl⟩

/-- The model recipient outputs a key exactly on the states reached by a
  completed run: `none` before accepting, `some` on the state installed by
  a successful `accept`. -/
lemma recipient_outputsOnlyAtCompletion
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    (recipient P hasOPK).OutputsOnlyAtCompletion := by
  unfold Party.OutputsOnlyAtCompletion
  refine ⟨?_, ?_, ?_⟩
  · intro i r hr out hout
    obtain ⟨opkB, -, hr⟩ := support_bind_exists hr
    obtain ⟨pqpkB, -, hr⟩ := support_bind_exists hr
    obtain ⟨bundle, -, hr⟩ := support_bind_exists hr
    obtain rfl := eq_of_mem_support_pure hr
    exact eq_of_mem_support_pure hout
  · intro st w st' hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ctx
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain ⟨conf, -, hst'⟩ := support_bind_exists hst'
          exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)
  · intro st w st' w' done hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ctx
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain ⟨conf, -, hst'⟩ := support_bind_exists hst'
          obtain ⟨rfl, -, rfl⟩ :=
            Party.StepResult.acceptAndSend.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)

/-- The model recipient's output function has no effect: on every state it
  returns a fixed value. -/
lemma recipient_pureOutput
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    (recipient P hasOPK).PureOutput := by
  rintro (p | k) <;> exact ⟨_, rfl⟩

/-- The model 2-round initiator outputs a key exactly on the state installed
  by a successful `initiate`. -/
lemma initiatorNoConfirm_outputsOnlyAtCompletion
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    (initiatorNoConfirm P).OutputsOnlyAtCompletion := by
  unfold Party.OutputsOnlyAtCompletion
  refine ⟨?_, ?_, ?_⟩
  · intro i r hr out hout
    obtain rfl := eq_of_mem_support_pure hr
    exact eq_of_mem_support_pure hout
  · intro st w st' hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ⟨im', ctx⟩ <;>
          exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)
  · intro st w st' w' done hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ⟨im', ctx⟩
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain ⟨rfl, -, rfl⟩ :=
            Party.StepResult.acceptAndSend.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)

/-- The model 2-round initiator's output function has no effect: on every state
  it returns a fixed value. -/
lemma initiatorNoConfirm_pureOutput
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    (initiatorNoConfirm P).PureOutput := by
  rintro (p | k) <;> exact ⟨_, rfl⟩

/-- The model 2-round recipient outputs a key exactly on the state installed
  by a successful `accept`. -/
lemma recipientNoConfirm_outputsOnlyAtCompletion
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    (recipientNoConfirm P hasOPK).OutputsOnlyAtCompletion := by
  unfold Party.OutputsOnlyAtCompletion
  refine ⟨?_, ?_, ?_⟩
  · intro i r hr out hout
    obtain ⟨opkB, -, hr⟩ := support_bind_exists hr
    obtain ⟨pqpkB, -, hr⟩ := support_bind_exists hr
    obtain ⟨bundle, -, hr⟩ := support_bind_exists hr
    obtain rfl := eq_of_mem_support_pure hr
    exact eq_of_mem_support_pure hout
  · intro st w st' hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ctx
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain rfl := Party.StepResult.complete.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)
  · intro st w st' w' done hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ctx <;>
          exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)

/-- The model 2-round recipient's output function has no effect: on every state
  it returns a fixed value. -/
lemma recipientNoConfirm_pureOutput
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    (recipientNoConfirm P hasOPK).PureOutput := by
  rintro (p | k) <;> exact ⟨_, rfl⟩

/-- Under the correctness hypotheses, an honest run of the T=Bob parties on
  keys drawn from `setup` transfers exactly the scheme's 3 messages. -/
lemma runHonest_length_initiator
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    {uk : InitiatorParameters F G SPK Msg} {tk : RecipientIdentity F G SPK SSK S}
    (hsetup : (uk, tk) ∈ support (setup P msg))
    {uOut tOut : Option (Option K)} {ms : List (Message G PQPK CT S C IdC IdK)}
    (hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (initiator P) (recipient P hasOPK)
      uk tk (3 + 1))) :
    ms.length = 3 := by
  simp only [setup, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsetup
  obtain ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB,
    huk, htk⟩ := hsetup
  subst huk htk
  exact (run_support_initiator P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB
    hspkSigB hrun).2

/-- Under the correctness hypotheses, an honest run of the T=Alice parties
  on keys drawn from `setup` transfers exactly the scheme's 2 messages. -/
lemma runHonest_length_recipient
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    {uk : InitiatorParameters F G SPK Msg} {tk : RecipientIdentity F G SPK SSK S}
    (hsetup : (uk, tk) ∈ support (setup P msg))
    {uOut tOut : Option (Option K)} {ms : List (Message G PQPK CT S C IdC IdK)}
    (hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (recipientNoConfirm P hasOPK)
      (initiatorNoConfirm P) tk uk (2 + 1))) :
    ms.length = 2 := by
  simp only [setup, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsetup
  obtain ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB,
    huk, htk⟩ := hsetup
  subst huk htk
  exact (run_support_recipient P hasOPK hsig hkem haead msg hikA hikB hsigkB hspkB
    hspkSigB hrun).2

end Protocols.PQXDH
