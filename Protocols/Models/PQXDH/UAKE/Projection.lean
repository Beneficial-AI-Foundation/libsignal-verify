/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.Models.PQXDH.UAKE.Defs
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Transport

/-!
# The projection of the PQXDH model onto key-only parties

`initiator` and `recipient` keep their session context once they accept, so that original-key
partnering can read the key material `km`. `initiatorKeyOnly` and `recipientKeyOnly` are the
parties as they were before that change: once a party accepts, it keeps only its key. They are a
reference for this file, and no security theorem uses them.

`initiator_sim` and `recipient_sim` show that the parties of `uakeInitiator` simulate the key-only
parties when each retained context is replaced by its key. The transport theorems of
`Transport.lean` then give the projection. On every adversary, the challenge stage of
`uakeInitiatorKeyOnly` is that of `uakeInitiator` with each retained context replaced by its key:
the same challenge key, transcripts, clock, session keys, reveal flags and adversary state
(`challengeSession_projection`). The DF'17 experiment and its advantage are equal for the two
schemes (`uakeInitiator_Exp_projection`, `uakeInitiator_advantage_projection`), and every
adversary of `uakeInitiator` has the same advantage against both
(`uakeInitiator_advantage_eq_keyOnly`).

Both kinds of parties call the same `initiate` and `accept`, which store `km` in the context, so
the projection says nothing about those two functions. It does not apply to `PartneredExp` over
`originalKeyPartnering`, which reads the contexts that the key-only parties drop.

The key-only parties copy the text of Galois's `initiator` and `recipient`. The other definitions
and the proofs in this file are AI-written.
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

/-- Alice's party as it was before she kept her session context: once `confirm` accepts Bob's
  confirmation, she keeps only the key that `confirm` returns. A reference for the projection
  lemmas; no security theorem uses it. -/
def initiatorKeyOnly :
    Party ProbComp (InitiatorParameters F G Msg) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K SS ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiate P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr SK) => pure (some (some SK))
    | _ => pure none

/-- Bob's party as it was before he kept his session context: once `accept` succeeds, he keeps only
  the key `ctx.sk`. A reference for the projection lemmas; no security theorem uses it. -/
def recipientKeyOnly :
    Party ProbComp (RecipientIdentity F G S) (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G PQPK PQSK S ⊕ K
  init := fun idn => do
    let opkB ← genOPK P.gen hasOPK
    let pqpkB ← P.pqkem.keygen
    let p : RecipientParameters F G PQPK PQSK S :=
      { ikB := idn.ikB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => do
            let conf ← P.aead.encrypt ctx.kb ctx.ad ctx.msg
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

/-- `uakeInitiator` with the key-only parties, the same number of rounds and the same setup. -/
def uakeInitiatorKeyOnly :
    UAKE.Scheme ProbComp K (InitiatorParameters F G Msg) (RecipientIdentity F G S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiatorKeyOnly P
  T := recipientKeyOnly P hasOPK

/-- Alice's state with a retained session context replaced by its key. -/
def initiatorForget :
    InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K SS ⊕
        SessionContext G PQPK Msg K SS →
      InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K SS ⊕ K
  | .inl p => .inl p
  | .inr (.inl ctx) => .inr (.inl ctx)
  | .inr (.inr ctx) => .inr (.inr ctx.sk)

/-- Bob's state with a retained session context replaced by its key. -/
def recipientForget :
    RecipientParameters F G PQPK PQSK S ⊕ SessionContext G PQPK Msg K SS →
      RecipientParameters F G PQPK PQSK S ⊕ K
  | .inl p => .inl p
  | .inr ctx => .inr ctx.sk

omit [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C] [DecidableEq IdC]
  [DecidableEq IdK] [SampleableType K] in
/-- Alice's party simulates the key-only party when her retained context is replaced by its key. -/
theorem initiator_sim : Party.Sim (initiator P) (initiatorKeyOnly P) id initiatorForget := by
  refine ⟨fun p => ?_, fun st w => ?_, fun st => ?_⟩
  · simp [initiator, initiatorKeyOnly, Party.InitResult.map, initiatorForget]
  · rcases st with p | ctx | ctx <;> cases w <;>
      simp only [initiator, initiatorKeyOnly, initiatorForget, map_pure, Party.StepResult.map,
        map_bind]
    · refine bind_congr fun r => ?_
      rcases r with _ | ⟨im, ctx⟩ <;> simp [Party.StepResult.map, initiatorForget]
    · unfold confirm
      split_ifs <;> simp [Party.StepResult.map, initiatorForget]
  · rcases st with p | ctx | ctx <;> rfl

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [SampleableType K] in
/-- Bob's party simulates the key-only party when his retained context is replaced by its key. -/
theorem recipient_sim :
    Party.Sim (recipient P hasOPK) (recipientKeyOnly P hasOPK) id recipientForget := by
  refine ⟨fun idn => ?_, fun st w => ?_, fun st => ?_⟩
  · simp [recipient, recipientKeyOnly, Party.InitResult.map, recipientForget, map_bind]
  · rcases st with p | ctx <;> cases w <;>
      simp only [recipient, recipientKeyOnly, recipientForget, map_pure, Party.StepResult.map,
        map_bind]
    refine bind_congr fun r => ?_
    rcases r with _ | ctx <;> simp [Party.StepResult.map, recipientForget]
  · rcases st with p | ctx <;> rfl

omit [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C] [SampleableType K] in
/-- The projection lemma for the challenge stage: on every adversary, the challenge stage of
  `uakeInitiatorKeyOnly` is that of `uakeInitiator` with each retained context replaced by its key.
  The challenge key, the transcripts, the clock, the session keys, the reveal flags and the
  adversary state are the same. -/
theorem challengeSession_projection (A : UAKE.Adversary (uakeInitiatorKeyOnly P msg hasOPK))
    (uk : InitiatorParameters F G Msg) (tk : RecipientIdentity F G S) :
    challengeSession ProbCompRuntime.probComp.toProbCompLift A uk tk =
      (fun r => (ChallengeResult.transport r.1,
          (r.2.1, Env.transport initiatorForget recipientForget r.2.2.1, r.2.2.2))) <$>
        challengeSession ProbCompRuntime.probComp.toProbCompLift
          (A.transport (proto₁ := uakeInitiator P msg hasOPK) id) uk tk :=
  challengeSession_transport (proto₁ := uakeInitiator P msg hasOPK)
    (proto₂ := uakeInitiatorKeyOnly P msg hasOPK) ProbCompRuntime.probComp.toProbCompLift
    (initiator_sim P) (recipient_sim P hasOPK) A uk tk

/-- The DF'17 experiment is the same for `uakeInitiator` and for its key-only parties. -/
theorem uakeInitiator_Exp_projection (A : UAKE.Adversary (uakeInitiatorKeyOnly P msg hasOPK)) :
    UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A =
      UAKE.Exp ProbCompRuntime.probComp.toProbCompLift
        (A.transport (proto₁ := uakeInitiator P msg hasOPK) id) :=
  Exp_transport (proto₁ := uakeInitiator P msg hasOPK)
    (proto₂ := uakeInitiatorKeyOnly P msg hasOPK) ProbCompRuntime.probComp.toProbCompLift
    (initiator_sim P) (recipient_sim P hasOPK) rfl
    (by simp [uakeInitiatorKeyOnly, uakeInitiator]) A

/-- The DF'17 advantage is the same for `uakeInitiator` and for its key-only parties. -/
theorem uakeInitiator_advantage_projection
    (A : UAKE.Adversary (uakeInitiatorKeyOnly P msg hasOPK)) :
    UAKE.advantage ProbCompRuntime.probComp A =
      UAKE.advantage ProbCompRuntime.probComp
        (A.transport (proto₁ := uakeInitiator P msg hasOPK) id) := by
  unfold UAKE.advantage
  rw [← uakeInitiator_Exp_projection P msg hasOPK A]

/-- Every adversary of `uakeInitiator` has the same DF'17 advantage against the key-only parties:
  keeping the session contexts leaves the advantage in `UAKE.Exp` unchanged. -/
theorem uakeInitiator_advantage_eq_keyOnly (B : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.advantage ProbCompRuntime.probComp B =
      UAKE.advantage ProbCompRuntime.probComp
        ({ State := B.State, challenge := B.challenge, post := B.post } :
          UAKE.Adversary (uakeInitiatorKeyOnly P msg hasOPK)) := by
  have h := uakeInitiator_advantage_projection P msg hasOPK
    ({ State := B.State, challenge := B.challenge, post := B.post } :
      UAKE.Adversary (uakeInitiatorKeyOnly P msg hasOPK))
  rw [h]
  rfl

end Protocols.Models.PQXDH
