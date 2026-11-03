/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.PQXDH.Correctness

/-!
# Fault fixtures for the correctness statements of the Full realization

The correctness statements of `Protocols.PQXDH` say that certain success events have
probability `1`, or at least `1 - δ`. A success event that a broken implementation also satisfies
would make such a statement vacuous. The UAKE correctness experiment `AKE.UAKE.CorrectExp`, from
PQXDH-model, counts a run in which either party outputs nothing as correct, so a realization that
always fails passes it.

The fixtures replace the extracted entry points by three broken ones, `EntryPoints.alwaysPanic`,
`EntryPoints.alwaysError` and `EntryPoints.alwaysDiverge`, and prove that each fails every
correctness statement for every `δ < 1`. The argument needs only that the initiator's entry point
never returns an agreement (`EntryPoints.NeverAgrees`). Then Alice never leaves her initial state
and outputs no key, so every success event has probability `0`. The fixtures assume no contract.
The `#guard_msgs` checks at the end record that no fixture depends on a stub.
-/

open OracleSpec OracleComp AKE AKE.UAKE ENNReal
open Aeneas Aeneas.Std
open libsignal_protocol
open Protocols.Realization

namespace Protocols.PQXDH

variable {Rand Msg C IdC IdK : Type}

/-- Entry points that always panic. -/
def EntryPoints.alwaysPanic : EntryPoints Rand where
  initiate _ _ _ _ := .fail .panic
  accept _ := .fail .panic

/-- Entry points that always return the protocol error `e`, leaving the generator state as it
was. -/
def EntryPoints.alwaysError (e : error.SignalProtocolError) : EntryPoints Rand where
  initiate _ _ _ r := .ok (.Err e, r)
  accept _ := .ok (.Err e)

/-- Entry points that never terminate. -/
def EntryPoints.alwaysDiverge : EntryPoints Rand where
  initiate _ _ _ _ := .div
  accept _ := .div

/-- The initiator's entry point never returns an agreement. -/
def EntryPoints.NeverAgrees (E : EntryPoints Rand) : Prop :=
  ∀ rng crng ip r (ag : InitiatorAgreement) r', E.initiate rng crng ip r ≠ .ok (.Ok ag, r')

theorem EntryPoints.alwaysPanic_neverAgrees :
    (EntryPoints.alwaysPanic : EntryPoints Rand).NeverAgrees := by
  intro _ _ _ _ _ _
  simp [EntryPoints.alwaysPanic]

theorem EntryPoints.alwaysError_neverAgrees (e : error.SignalProtocolError) :
    (EntryPoints.alwaysError e : EntryPoints Rand).NeverAgrees := by
  intro _ _ _ _ _ _
  simp [EntryPoints.alwaysError]

theorem EntryPoints.alwaysDiverge_neverAgrees :
    (EntryPoints.alwaysDiverge : EntryPoints Rand).NeverAgrees := by
  intro _ _ _ _ _ _
  simp [EntryPoints.alwaysDiverge]

section Core

variable (P : Params Rand Msg C IdC IdK) {E : EntryPoints Rand} (hasOPK : Bool)

/-- If the initiator never returns an agreement, the honest core run never reaches the
responder. -/
theorem coreHonestRun_snd_eq_none (hE : E.NeverAgrees) :
    ∀ x ∈ support (coreHonestRun P E hasOPK), x.2 = none := by
  intro x hx
  simp only [coreHonestRun, support_bind, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, ⟨resA, R'⟩, hres, hx⟩ := hx
  rw [mem_support_liftResult] at hres
  rcases resA with ag | e
  · exact absurd hres (hE _ _ _ _ ag R')
  · simp only [support_pure, Set.mem_singleton_iff] at hx
    rw [hx]

/-- Core completion has probability `0` when the initiator never returns an agreement. -/
theorem coreCompletionExp_eq_zero (hE : E.NeverAgrees) :
    rustRuntime.evalDist (coreCompletionExp P E hasOPK) {true} = 0 := by
  rw [probOutput_rustRuntime_eq_zero_iff]
  intro h
  simp only [coreCompletionExp, support_bind, Set.mem_iUnion, exists_prop] at h
  obtain ⟨x, hx, h⟩ := h
  rw [coreHonestRun_snd_eq_none P hasOPK hE x hx] at h
  rcases x with ⟨_ | _, _⟩ <;> simp at h

/-- Joint key-record agreement has probability `0` when the initiator never returns an
agreement. -/
theorem jointKeyExp_eq_zero (hE : E.NeverAgrees) :
    rustRuntime.evalDist (jointKeyExp P E hasOPK) {true} = 0 := by
  rw [probOutput_rustRuntime_eq_zero_iff]
  intro h
  simp only [jointKeyExp, support_bind, Set.mem_iUnion, exists_prop] at h
  obtain ⟨x, hx, h⟩ := h
  rw [coreHonestRun_snd_eq_none P hasOPK hE x hx] at h
  rcases x with ⟨_ | _, _⟩ <;> simp at h

end Core

section Wrapper

variable (P : Params Rand Msg C IdC IdK) {E : EntryPoints Rand}

/-- If the initiator never returns an agreement, Alice's step on a bundle never produces a
message. -/
theorem initiate_eq_none (hE : E.NeverAgrees) (p : InitiatorParameters Msg)
    (R : Rand) (b : FullBundle IdC IdK) :
    ∀ x ∈ support (initiate P E p R b), x = none := by
  intro x hx
  unfold initiate at hx
  split_ifs at hx
  · simpa using hx
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨_, -, _, -, _, -, hx⟩ := hx
  split_ifs at hx
  · simpa using hx
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨_, -, _, -, _, -, hx⟩ := hx
  split_ifs at hx
  · simpa using hx
  simp only [pure_bind, support_bind, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨_, -, ⟨res, R'⟩, hres, hx⟩ := hx
  rw [mem_support_liftResult] at hres
  rcases res with ag | e
  · exact absurd hres (hE _ _ _ _ ag R')
  · simpa using hx

/-- Alice's states before she has answered a bundle. -/
def AliceWaiting (st : InitiatorState Rand Msg) : Prop := ∃ p R, st = .start p R

/-- If the initiator never returns an agreement, Alice in the three-message scheme rejects every
message while she waits for a bundle. -/
theorem initiator_stuck [DecidableEq Msg] (hE : E.NeverAgrees) :
    ∀ st, AliceWaiting st → ∀ w r, r ∈ support ((initiator (C := C) (IdK := IdK) P E).step st w) →
      r = .reject := by
  rintro st ⟨p, R, rfl⟩ w r hr
  cases w with
  | bundle b =>
    have h : (initiator (C := C) (IdK := IdK) P E).step (.start p R) (.bundle b) =
        (initiate P E p R b >>= fun x => match x with
          | some (im, s, R') =>
              pure (.acceptAndSend (InitiatorState.sent s R') (.initial im) false)
          | none => pure .reject) := rfl
    rw [h, mem_support_bind_iff] at hr
    obtain ⟨x, hx, hr⟩ := hr
    rw [initiate_eq_none P hE p R b x hx, support_pure, Set.mem_singleton_iff] at hr
    exact hr
  | initial im =>
    have h : (initiator (C := C) (IdK := IdK) P E).step (.start p R) (.initial im) =
        pure .reject := rfl
    rwa [h, support_pure, Set.mem_singleton_iff] at hr
  | confirmation c =>
    have h : (initiator (C := C) (IdK := IdK) P E).step (.start p R) (.confirmation c) =
        pure .reject := rfl
    rwa [h, support_pure, Set.mem_singleton_iff] at hr

/-- If the initiator never returns an agreement, Alice in the two-message scheme rejects every
message while she waits for a bundle. -/
theorem initiatorNoConfirm_stuck (hE : E.NeverAgrees) :
    ∀ st, AliceWaiting st →
      ∀ w r, r ∈ support ((initiatorNoConfirm (C := C) (IdK := IdK) P E).step st w) →
        r = .reject := by
  rintro st ⟨p, R, rfl⟩ w r hr
  cases w with
  | bundle b =>
    have h : (initiatorNoConfirm (C := C) (IdK := IdK) P E).step (.start p R) (.bundle b) =
        (initiate P E p R b >>= fun x => match x with
          | some (im, s, _) => pure (.acceptAndSend (InitiatorState.done s) (.initial im) true)
          | none => pure .reject) := rfl
    rw [h, mem_support_bind_iff] at hr
    obtain ⟨x, hx, hr⟩ := hr
    rw [initiate_eq_none P hE p R b x hx, support_pure, Set.mem_singleton_iff] at hr
    exact hr
  | initial im =>
    have h : (initiatorNoConfirm (C := C) (IdK := IdK) P E).step (.start p R) (.initial im) =
        pure .reject := rfl
    rwa [h, support_pure, Set.mem_singleton_iff] at hr
  | confirmation c =>
    have h :
        (initiatorNoConfirm (C := C) (IdK := IdK) P E).step (.start p R) (.confirmation c) =
          pure .reject := rfl
    rwa [h, support_pure, Set.mem_singleton_iff] at hr

/-- Alice starts every session waiting for a bundle. -/
theorem initiator_init_waiting [DecidableEq Msg] (p : InitiatorParameters Msg) :
    ∀ r ∈ support ((initiator (C := C) (IdC := IdC) (IdK := IdK) P E).init p),
      AliceWaiting r.state := by
  intro r hr
  have h : (initiator (C := C) (IdC := IdC) (IdK := IdK) P E).init p =
      ((liftM P.coins : RustOracleComp unifSpec Rand) >>= fun R =>
        pure (.waitForMsg (InitiatorState.start p R))) := rfl
  rw [h, mem_support_bind_iff] at hr
  obtain ⟨R, -, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨p, R, rfl⟩

/-- Alice starts every session waiting for a bundle, in the two-message scheme. -/
theorem initiatorNoConfirm_init_waiting (p : InitiatorParameters Msg) :
    ∀ r ∈ support ((initiatorNoConfirm (C := C) (IdC := IdC) (IdK := IdK) P E).init p),
      AliceWaiting r.state := by
  intro r hr
  have h : (initiatorNoConfirm (C := C) (IdC := IdC) (IdK := IdK) P E).init p =
      ((liftM P.coins : RustOracleComp unifSpec Rand) >>= fun R =>
        pure (.waitForMsg (InitiatorState.start p R))) := rfl
  rw [h, mem_support_bind_iff] at hr
  obtain ⟨R, -, hr⟩ := hr
  rw [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact ⟨p, R, rfl⟩

/-- Wrapper agreement in the three-message scheme has probability `0` when the initiator never
returns an agreement: Alice never outputs a key. -/
theorem agreementExp_uakeInitiator_eq_zero [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (msg : Msg) (hasOPK : Bool) (hE : E.NeverAgrees) :
    rustRuntime.evalDist (agreementExp (uakeInitiator P E msg hasOPK)) {true} = 0 := by
  rw [probOutput_rustRuntime_eq_zero_iff]
  intro h
  simp only [agreementExp, support_bind, Set.mem_iUnion, exists_prop] at h
  obtain ⟨⟨uk, tk⟩, -, ⟨uOut, tOut, ms⟩, hrun, h⟩ := h
  obtain ⟨st, ⟨p, R, rfl⟩, hout⟩ := Party.runHonest_fst_of_stuck (uakeInitiator P E msg hasOPK).U
    (uakeInitiator P E msg hasOPK).T AliceWaiting (initiator_stuck P hE)
    (initiator_init_waiting P) uk tk _ _ hrun
  simp only [uakeInitiator, initiator, InitiatorState.jointKeys, Option.map_none, support_pure,
    Set.mem_singleton_iff] at hout
  subst hout
  simp at h

/-- Wrapper agreement in the two-message scheme has probability `0` when the initiator never
returns an agreement: Alice, the authenticated party, never outputs a key, and agreement needs
both keys. -/
theorem agreementExp_uakeRecipient_eq_zero [DecidableEq IdC] [DecidableEq IdK]
    (msg : Msg) (hasOPK : Bool) (hE : E.NeverAgrees) :
    rustRuntime.evalDist (agreementExp (uakeRecipient P E msg hasOPK)) {true} = 0 := by
  rw [probOutput_rustRuntime_eq_zero_iff]
  intro h
  simp only [agreementExp, support_bind, Set.mem_iUnion, exists_prop] at h
  obtain ⟨⟨uk, tk⟩, -, ⟨uOut, tOut, ms⟩, hrun, h⟩ := h
  obtain ⟨st, ⟨p, R, rfl⟩, hout⟩ := Party.runHonest_snd_of_stuck (uakeRecipient P E msg hasOPK).U
    (uakeRecipient P E msg hasOPK).T AliceWaiting (initiatorNoConfirm_stuck P hE)
    (initiatorNoConfirm_init_waiting P) uk tk _ _ hrun
  simp only [uakeRecipient, initiatorNoConfirm, InitiatorState.jointKeys, Option.map_none,
    support_pure, Set.mem_singleton_iff] at hout
  subst hout
  simp only [support_pure, Set.mem_singleton_iff, Option.join_none] at h
  obtain ⟨h₁, h₂⟩ := of_decide_eq_true h.symm
  rw [h₂] at h₁
  exact absurd h₁ (by simp)

end Wrapper

section Fixtures

variable (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]

/-- A positive lower bound `1 - δ` is not met by probability `0`. -/
theorem not_one_sub_le_zero {δ : ℝ≥0∞} (hδ : δ < 1) : ¬ 1 - δ ≤ 0 := by
  rw [nonpos_iff_eq_zero, tsub_eq_zero_iff_le]
  exact not_le.mpr hδ

/-- Entry points that never return an agreement fail all three correctness statements: core
completion does not hold with probability `1`, and for every `δ < 1` neither joint key-record
agreement nor wrapper agreement (in either scheme) holds with probability at least `1 - δ`. -/
theorem fails_of_neverAgrees {E : EntryPoints Rand} (hE : E.NeverAgrees) {δ : ℝ≥0∞}
    (hδ : δ < 1) :
    rustRuntime.evalDist (coreCompletionExp P E hasOPK) {true} ≠ 1 ∧
      ¬ 1 - δ ≤ rustRuntime.evalDist (jointKeyExp P E hasOPK) {true} ∧
      ¬ 1 - δ ≤ rustRuntime.evalDist (agreementExp (uakeInitiator P E msg hasOPK)) {true} ∧
      ¬ 1 - δ ≤
        rustRuntime.evalDist (agreementExp (uakeRecipient P E msg hasOPK)) {true} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coreCompletionExp_eq_zero P hasOPK hE]
    exact zero_ne_one
  · rw [jointKeyExp_eq_zero P hasOPK hE]
    exact not_one_sub_le_zero hδ
  · rw [agreementExp_uakeInitiator_eq_zero P msg hasOPK hE]
    exact not_one_sub_le_zero hδ
  · rw [agreementExp_uakeRecipient_eq_zero P msg hasOPK hE]
    exact not_one_sub_le_zero hδ

/-- The always-panic fixture: entry points that always panic fail every correctness statement,
for every `δ < 1`. -/
theorem alwaysPanic_fails {δ : ℝ≥0∞} (hδ : δ < 1) :
    rustRuntime.evalDist (coreCompletionExp P EntryPoints.alwaysPanic hasOPK) {true} ≠ 1 ∧
      ¬ 1 - δ ≤ rustRuntime.evalDist (jointKeyExp P EntryPoints.alwaysPanic hasOPK) {true} ∧
      ¬ 1 - δ ≤ rustRuntime.evalDist
        (agreementExp (uakeInitiator P EntryPoints.alwaysPanic msg hasOPK)) {true} ∧
      ¬ 1 - δ ≤ rustRuntime.evalDist
        (agreementExp (uakeRecipient P EntryPoints.alwaysPanic msg hasOPK)) {true} :=
  fails_of_neverAgrees P msg hasOPK EntryPoints.alwaysPanic_neverAgrees hδ

/-- The always-error fixture: entry points that always return the protocol error `e` fail every
correctness statement, for every `δ < 1`. -/
theorem alwaysError_fails (e : error.SignalProtocolError) {δ : ℝ≥0∞} (hδ : δ < 1) :
    rustRuntime.evalDist (coreCompletionExp P (EntryPoints.alwaysError e) hasOPK) {true} ≠
        1 ∧
      ¬ 1 - δ ≤
        rustRuntime.evalDist (jointKeyExp P (EntryPoints.alwaysError e) hasOPK) {true} ∧
      ¬ 1 - δ ≤ rustRuntime.evalDist
        (agreementExp (uakeInitiator P (EntryPoints.alwaysError e) msg hasOPK)) {true} ∧
      ¬ 1 - δ ≤ rustRuntime.evalDist
        (agreementExp (uakeRecipient P (EntryPoints.alwaysError e) msg hasOPK)) {true} :=
  fails_of_neverAgrees P msg hasOPK (EntryPoints.alwaysError_neverAgrees e) hδ

/-- The always-diverge fixture: entry points that never terminate fail every correctness
statement, for every `δ < 1`. -/
theorem alwaysDiverge_fails {δ : ℝ≥0∞} (hδ : δ < 1) :
    rustRuntime.evalDist (coreCompletionExp P EntryPoints.alwaysDiverge hasOPK) {true} ≠
        1 ∧
      ¬ 1 - δ ≤
        rustRuntime.evalDist (jointKeyExp P EntryPoints.alwaysDiverge hasOPK) {true} ∧
      ¬ 1 - δ ≤ rustRuntime.evalDist
        (agreementExp (uakeInitiator P EntryPoints.alwaysDiverge msg hasOPK)) {true} ∧
      ¬ 1 - δ ≤ rustRuntime.evalDist
        (agreementExp (uakeRecipient P EntryPoints.alwaysDiverge msg hasOPK)) {true} :=
  fails_of_neverAgrees P msg hasOPK EntryPoints.alwaysDiverge_neverAgrees hδ

end Fixtures

end Protocols.PQXDH

/-! ## Dependencies of the fixtures

No fixture depends on a stub. The other constants are opaque leaves of the extraction that the
definitions of the wrapper mention. The fixtures assume nothing about them. -/

/--
info: 'Protocols.PQXDH.alwaysPanic_fails' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.verify_signature_for_multipart_message,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.alwaysPanic_fails

/--
info: 'Protocols.PQXDH.alwaysError_fails' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.verify_signature_for_multipart_message,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.alwaysError_fails

/--
info: 'Protocols.PQXDH.alwaysDiverge_fails' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.verify_signature_for_multipart_message,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.alwaysDiverge_fails
