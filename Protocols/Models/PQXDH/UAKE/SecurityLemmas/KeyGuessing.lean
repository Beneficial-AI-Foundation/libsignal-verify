/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.OracleInvariants
import Protocols.ToVCVio.EvalDist.Monad.Basic
import Protocols.ToVCVio.OracleComp.QueryTracking.QueryBound

/-!
# The KEM-key guessing bound (hop 4)

The proof of `Protocols.Models.PQXDH.pqpkGuessedProb_le`. The bad event `pqpkGuessed` asks whether a
T session's KEM public key repeats an earlier session's key or the key of a bundle that the
challenge session accepted before that session was opened. Each session draws its key afresh
from `P.pqkem.keygen`, after everything it is compared with is already fixed, so each draw hits
at most `n + 1` known keys, where `n` is the number of sessions opened so far.

The argument is a potential bound on the simulated challenge stage: with `b` openings left in
the budget and `n` sessions open, the probability of ending in the bad event is at most
`ε * b * (n + b)` when the current state is not bad, where `ε` bounds the probability of any
single public key. The bound for an arbitrary stateful oracle implementation,
`OracleComp.probEvent_simulateQ_bad_le`, is in
`Protocols/ToVCVio/OracleComp/QueryTracking/QueryBound.lean`. This file instantiates it with the
UAKE oracle. The facts about that oracle that hold for every scheme (`Env.openNext`,
`Env.SessionsStarted` and their lemmas) are in
`Protocols/ToVCVio/CryptoFoundations/AKE/UAKE/OracleInvariants.lean`. What stays here depends on
PQXDH: the bad event `badEnv`, the key set `keySet`, and the proofs that the oracle keeps
`SessionsStarted`, changes the bad event only at `openT`, and hits `keySet` with probability at
most `ε` per key.

The lemma statements and proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.Models.PQXDH.KeyGuessing

section Model

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- The UAKE oracle of the challenge stage. -/
noncomputable abbrev oracle (tk : RecipientIdentity F G SPK SSK S) :
    QueryImpl (unifSpec + oracleSpec K (Message G PQPK CT S C IdC IdK))
      (StateT (Env (uakeInitiator P msg hasOPK)) ProbComp) :=
  oracleImpl ProbCompRuntime.probComp.toProbCompLift (uakeInitiator P msg hasOPK) tk

/-- The challenge result read off an environment, with no challenge key. -/
def envResult (env : Env (uakeInitiator P msg hasOPK)) :
    ChallengeResult (uakeInitiator P msg hasOPK) :=
  ⟨none, env.challenge.transcript, env.tSessions.map (·.transcript)⟩

/-- The bad event of hop 4, evaluated on an environment. -/
def badEnv [DecidableEq PQPK] (env : Env (uakeInitiator P msg hasOPK)) : Bool :=
  pqpkGuessed P msg hasOPK (envResult P msg hasOPK env)

/-- The KEM public keys a newly opened session could repeat: those of the open sessions and
that of the bundle the challenge has accepted, if any. -/
def keySet [DecidableEq PQPK] (env : Env (uakeInitiator P msg hasOPK)) : Finset PQPK :=
  ((oracleBundles P msg hasOPK (envResult P msg hasOPK env)).map (·.pqpkB.1) ++
    ((challengeBundle P msg hasOPK (envResult P msg hasOPK env)).map
      (·.pqpkB.1)).toList).toFinset

theorem keySet_card_le [DecidableEq PQPK] (env : Env (uakeInitiator P msg hasOPK)) :
    (keySet P msg hasOPK env).card ≤ env.tSessions.length + 1 := by
  unfold keySet
  refine (List.toFinset_card_le _).trans ?_
  have h1 : (oracleBundles P msg hasOPK (envResult P msg hasOPK env)).length ≤
      env.tSessions.length := by
    simp only [oracleBundles, envResult]
    exact (List.length_filterMap_le _ _).trans (by simp)
  have h2 : ((challengeBundle P msg hasOPK (envResult P msg hasOPK env)).map
      (·.pqpkB.1)).toList.length ≤ 1 := by
    cases challengeBundle P msg hasOPK (envResult P msg hasOPK env) <;> simp
  simp only [List.length_append, List.length_map]
  omega

/-- Opening a session with bundle `bd` from a good state makes the state bad only if the key of
`bd` is already in `keySet`. -/
theorem mem_keySet_of_badEnv_openNext [DecidableEq PQPK]
    (env : Env (uakeInitiator P msg hasOPK)) (hbad : badEnv P msg hasOPK env = false)
    (st : (uakeInitiator P msg hasOPK).T.State) (bd : PreKeyBundle G PQPK S IdC IdK)
    (h : badEnv P msg hasOPK (env.openNext (.speakFirst st (.bundle bd))) = true) :
    bd.pqpkB.1 ∈ keySet P msg hasOPK env := by
  simp only [badEnv, pqpkGuessed, oracleBundles, transcriptBundle, envResult, List.filterMap_map,
    Function.comp_apply, transcriptStart, List.any_map, challengeBundle, Bool.or_eq_false_iff,
    Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, Env.openNext, recordOpt,
    Party.InitResult.opening, recordOne, List.nil_append, Party.InitResult.state, List.map_append,
    List.map_cons, List.map_nil, List.filterMap_append, List.head?_cons, Option.some.injEq,
    List.filterMap_cons_some, List.filterMap_nil, List.nodup_append, List.nodup_cons,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, List.mem_map, List.mem_filterMap,
    List.mem_cons, or_false, ne_eq, forall_eq, forall_exists_index, and_imp, true_and,
    List.any_append, List.any_cons, Option.any_some, Option.map_some, List.any_nil, Bool.or_false,
    Bool.or_eq_true, Bool.not_true, decide_eq_false_iff_not, not_and, not_forall,
    Decidable.not_not, keySet, List.toFinset_append, Finset.mem_union,
    List.mem_toFinset, Option.mem_toList, Option.map_eq_some_iff] at hbad h ⊢
  rcases h with h | h
  · obtain ⟨x, y, s, hs, hy, hyx, rfl⟩ := h hbad.1
    exact Or.inl ⟨y, ⟨s, hs, hy⟩, hyx⟩
  · right
    obtain ⟨-, h2⟩ := hbad
    rcases hh : (env.challenge.transcript).entries.head? with _ | ⟨m, tc⟩
    · simp [hh] at h
    · cases m with
      | bundle b =>
        simp only [hh, Option.map_some, Option.any_some, Bool.or_eq_true, List.any_eq_true,
          Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_false, not_and,
          Bool.not_eq_true, Option.some.injEq, exists_eq_left'] at h h2 ⊢
        rcases h with ⟨x, hx, h1, h3⟩ | ⟨h1, -⟩
        · simp [h2 x hx h1] at h3
        · exact h1
      | initial _ => simp [hh] at h
      | confirmation _ => simp [hh] at h

/-- The bundle carried by a transcript's first entry, read from that entry alone. -/
def headBundle (e : Option (Message G PQPK CT S C IdC IdK × ℕ)) :
    Option (PreKeyBundle G PQPK S IdC IdK) :=
  match e with
  | some (Message.bundle b, _) => some b
  | _ => none

/-- `pqpkGuessed` as a function of the first entries of the transcripts. -/
def pgHeads [DecidableEq PQPK] (hc : Option (Message G PQPK CT S C IdC IdK × ℕ))
    (hs : List (Option (Message G PQPK CT S C IdC IdK × ℕ))) : Bool :=
  !decide ((hs.filterMap headBundle).map (·.pqpkB.1)).Nodup ||
    ((headBundle hc).any fun b => (hc.map Prod.snd).any fun tc =>
      hs.any fun e => ((headBundle e).any fun b' => decide (b.pqpkB.1 = b'.pqpkB.1)) &&
        (e.map Prod.snd).any fun ti => decide (tc < ti))

theorem badEnv_eq_pgHeads [DecidableEq PQPK] (env : Env (uakeInitiator P msg hasOPK)) :
    badEnv P msg hasOPK env = pgHeads (env.challenge.transcript).entries.head?
      (env.tSessions.map (·.transcript.entries.head?)) := by
  simp only [badEnv, envResult, pqpkGuessed, pgHeads, oracleBundles, challengeBundle,
    transcriptBundle, transcriptStart, List.filterMap_map, List.any_map]
  rfl

/-- Replacing a session by one whose transcript has the same first entry changes neither the
bad event nor the number of sessions. -/
theorem badEnv_set_of_head [DecidableEq PQPK] (env : Env (uakeInitiator P msg hasOPK))
    {sid : ℕ} {t : TSession (uakeInitiator P msg hasOPK)} (hs : env.tSessions[sid]? = some t)
    (t' : TSession (uakeInitiator P msg hasOPK))
    (ht' : (t'.transcript).entries.head? = (t.transcript).entries.head?) (c : ℕ) (d : Bool) :
    badEnv P msg hasOPK ⟨c, env.challenge, d, env.tSessions.set sid t'⟩ =
        badEnv P msg hasOPK env ∧
      (env.tSessions.set sid t').length = env.tSessions.length := by
  refine ⟨?_, by simp⟩
  rw [badEnv_eq_pgHeads, badEnv_eq_pgHeads]
  congr 1
  rw [List.map_set]
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hs
  have h' := List.set_getElem_self (as := env.tSessions.map (·.transcript.entries.head?))
    (i := sid) (by simpa using hlt)
  simpa [hget, ht'] using h'

/-- Extending the challenge transcript by entries stamped from the current clock on changes
neither the bad event nor the sessions: a newly set challenge head is later than every session
head, so it predicts no existing session. -/
theorem badEnv_challenge_append [DecidableEq PQPK] (env : Env (uakeInitiator P msg hasOPK))
    (h : env.SessionsStarted) (c : ℕ) (st : (uakeInitiator P msg hasOPK).U.State)
    (tr : Transcript (Message G PQPK CT S C IdC IdK)) (d : Bool)
    (w : Message G PQPK CT S C IdC IdK) (rest : List (Message G PQPK CT S C IdC IdK × ℕ))
    (htr : tr.entries = (env.challenge.transcript).entries ++ (w, env.clock) :: rest) :
    badEnv P msg hasOPK ⟨c, ⟨st, tr⟩, d, env.tSessions⟩ = badEnv P msg hasOPK env ∧
      env.tSessions.length = env.tSessions.length := by
  refine ⟨?_, rfl⟩
  rw [badEnv_eq_pgHeads, badEnv_eq_pgHeads, htr]
  rcases hc : (env.challenge.transcript).entries with _ | ⟨e, es⟩
  · cases w with
    | bundle b =>
      simp only [List.nil_append, List.head?_cons, List.head?_nil, pgHeads, headBundle,
        Option.any_some, Option.map_some, Option.map_none, Option.any_none, Bool.or_false]
      refine (fun X Y (hY : Y = false) => by simp [hY] :
        ∀ X Y : Bool, Y = false → (X || Y) = X) _ _ ?_
      rw [List.any_eq_false]
      intro x hx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      obtain ⟨e', es', he', hlt⟩ := h s hs
      simp [he', Nat.not_lt.2 hlt.le]
    | initial _ => simp [pgHeads, headBundle]
    | confirmation _ => simp [pgHeads, headBundle]
  · simp

theorem oracle_inv (tk : RecipientIdentity F G SPK SSK S) (t)
    (env : Env (uakeInitiator P msg hasOPK)) (h : env.SessionsStarted) :
    ∀ z ∈ support ((oracle P msg hasOPK tk t).run env), z.2.SessionsStarted := by
  intro z hz
  rcases t with n | op
  · simp only [add_apply_inl, oracle, oracleImpl, HasQuery.toQueryImpl_apply,
      HasQuery.instOfMonadLift_query, QueryImpl.add_apply_inl, StateT.run_monadLift, monadLift_self,
      bind_pure_comp, support_map] at hz
    obtain ⟨a, -, rfl⟩ := hz
    exact h
  · cases op with
    | openT =>
      rw [oracleImpl_openT_run, mem_support_bind_iff] at hz
      obtain ⟨r, hr, hz⟩ := hz
      have hinit : (uakeInitiator P msg hasOPK).T.init tk = (recipient P hasOPK).init tk := rfl
      rw [hinit] at hr
      simp only [recipient] at hr
      obtain ⟨opk, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
      obtain ⟨kp, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
      obtain ⟨bd, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
      have hr' : r = _ := hr
      subst hr'
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      intro s hs
      simp only [Env.openNext, Party.InitResult.opening, recordOpt, recordOne, List.nil_append,
        Party.InitResult.state, List.mem_append, List.mem_singleton] at hs ⊢
      rcases hs with hs | rfl
      · obtain ⟨e, es, he, hlt⟩ := h s hs
        exact ⟨e, es, he, by omega⟩
      · exact ⟨_, [], rfl, by simp⟩
    | stepT sid w =>
      simp only [oracle, oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [add_apply_inr, bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, hs,
          StateT.run_pure, support_pure] at hz
        subst hz
        exact h
      · rcases hk : t.key with _ | key
        · simp only [add_apply_inr, bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get,
            hs, hk, StateT.run_monadLift, monadLift_self, bind_map_left] at hz
          obtain ⟨res, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
          have hle : ∀ k, env.clock ≤ env.clock + k := fun k => Nat.le_add_right _ _
          cases res with
          | reject =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact h
          | acceptAndSend st' w' done =>
            cases done
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_map, StateT.run_set, map_pure,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz
              exact env.sessionsStarted_set_extend h hs _ _ (by simp [recordOne]; rfl) _
                (by simp [recordOne]; omega) _ _
            · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
                bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
                support_map, Set.mem_image] at hz
              obtain ⟨y, -, hz⟩ := hz
              subst hz
              exact env.sessionsStarted_set_extend h hs _ _ (by simp [recordOne]; rfl) _
                (by simp [recordOne]; omega) _ _
          | complete st' =>
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
              StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map, Set.mem_image]
              at hz
            obtain ⟨y, -, hz⟩ := hz
            subst hz
            exact env.sessionsStarted_set_extend h hs _ _ (by simp [recordOne]; rfl) _
              (by simp [recordOne]) _ _
        · simp only [add_apply_inr, bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get,
            hs, hk, StateT.run_pure, support_pure] at hz
          subst hz
          exact h
    | revealT sid =>
      simp only [oracle, oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hs,
          StateT.run_pure, support_pure] at hz
        subst hz
        exact h
      · rcases hk : t.key with _ | key
        · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
            hs, hk, StateT.run_pure, support_pure] at hz
          subst hz
          exact h
        · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
            hs, hk, StateT.run_map, StateT.run_set, map_pure, support_pure] at hz
          subst hz
          intro s hs'
          rcases List.mem_or_eq_of_mem_set hs' with hs' | rfl
          · exact h s hs'
          · exact h t (List.mem_of_getElem? hs)
    | stepChallenge w =>
      simp only [oracle, oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      by_cases hd : env.challengeDone = true
      · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hd,
          ↓reduceIte, StateT.run_pure, support_pure] at hz
        subst hz
        exact h
      · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hd,
          Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
          bind_map_left] at hz
        obtain ⟨res, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        cases res with
        | reject =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact h
        | acceptAndSend st' w' done =>
          simp only [StateT.run_map, StateT.run_set, map_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact env.sessionsStarted_clock_mono h _ (by simp [recordOne]; omega) _ _
        | complete st' =>
          simp only [StateT.run_map, StateT.run_set, map_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact env.sessionsStarted_clock_mono h _ (by simp [recordOne]) _ _

theorem oracle_free [DecidableEq PQPK] (tk : RecipientIdentity F G SPK SSK S) (t)
    (ht : t ≠ Sum.inr .openT) (env : Env (uakeInitiator P msg hasOPK))
    (h : env.SessionsStarted) :
    ∀ z ∈ support ((oracle P msg hasOPK tk t).run env),
      badEnv P msg hasOPK z.2 = badEnv P msg hasOPK env ∧
        z.2.tSessions.length = env.tSessions.length := by
  intro z hz
  rcases t with n | op
  · simp only [add_apply_inl, oracle, oracleImpl, HasQuery.toQueryImpl_apply,
      HasQuery.instOfMonadLift_query, QueryImpl.add_apply_inl, StateT.run_monadLift, monadLift_self,
      bind_pure_comp, support_map] at hz
    obtain ⟨a, -, rfl⟩ := hz
    exact ⟨rfl, rfl⟩
  · cases op with
    | openT => exact absurd rfl ht
    | revealT sid =>
      simp only [oracle, oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hs,
          StateT.run_pure, support_pure] at hz
        subst hz
        exact ⟨rfl, rfl⟩
      · rcases hk : t.key with _ | key
        · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
            hs, hk, StateT.run_pure, support_pure] at hz
          subst hz
          exact ⟨rfl, rfl⟩
        · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
            hs, hk, StateT.run_map, StateT.run_set, map_pure, support_pure] at hz
          subst hz
          exact badEnv_set_of_head P msg hasOPK env hs ⟨t.state, t.transcript, some key, true⟩ rfl
            _ _
    | stepT sid w =>
      simp only [oracle, oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [add_apply_inr, bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, hs,
          StateT.run_pure, support_pure] at hz
        subst hz
        exact ⟨rfl, rfl⟩
      · obtain ⟨e, es, he, -⟩ := h t (List.mem_of_getElem? hs)
        rcases hk : t.key with _ | key
        · simp only [add_apply_inr, bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get,
            hs, hk, StateT.run_monadLift, monadLift_self, bind_map_left] at hz
          obtain ⟨res, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
          cases res with
          | reject =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            exact ⟨rfl, rfl⟩
          | acceptAndSend st' w' done =>
            cases done
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_map, StateT.run_set, map_pure,
                support_pure, Set.mem_singleton_iff] at hz
              subst hz
              exact badEnv_set_of_head P msg hasOPK env hs _ (by simp [recordOne, he]) _ _
            · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
                bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
                support_map, Set.mem_image] at hz
              obtain ⟨y, -, hz⟩ := hz
              subst hz
              exact badEnv_set_of_head P msg hasOPK env hs _ (by simp [recordOne, he]) _ _
          | complete st' =>
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
              StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map, Set.mem_image]
              at hz
            obtain ⟨y, -, hz⟩ := hz
            subst hz
            exact badEnv_set_of_head P msg hasOPK env hs _ (by simp [recordOne, he]) _ _
        · simp only [add_apply_inr, bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get,
            hs, hk, StateT.run_pure, support_pure] at hz
          subst hz
          exact ⟨rfl, rfl⟩
    | stepChallenge w =>
      simp only [oracle, oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      by_cases hd : env.challengeDone = true
      · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hd,
          ↓reduceIte, StateT.run_pure, support_pure] at hz
        subst hz
        exact ⟨rfl, rfl⟩
      · simp only [add_apply_inr, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hd,
          Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
          bind_map_left] at hz
        obtain ⟨res, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        cases res with
        | reject =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨rfl, rfl⟩
        | acceptAndSend st' w' done =>
          simp only [StateT.run_map, StateT.run_set, map_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact badEnv_challenge_append P msg hasOPK env h _ _ _ _ w [(w', env.clock + 1)]
            (by simp [recordOne])
        | complete st' =>
          simp only [StateT.run_map, StateT.run_set, map_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact badEnv_challenge_append P msg hasOPK env h _ _ _ _ w [] (by simp [recordOne])

theorem oracle_hit [DecidableEq PQPK] (tk : RecipientIdentity F G SPK SSK S) (ε : ℝ≥0∞)
    (hpk : ∀ pk, Pr[= pk | Prod.fst <$> P.pqkem.keygen] ≤ ε) (t)
    (ht : t = Sum.inr .openT) (env : Env (uakeInitiator P msg hasOPK))
    (hbad : badEnv P msg hasOPK env = false) :
    Pr[ fun z => badEnv P msg hasOPK z.2 = true | (oracle P msg hasOPK tk t).run env] ≤
      ε * ((env.tSessions.length + 1 : ℕ) : ℝ≥0∞) := by
  subst ht
  rw [oracleImpl_openT_run]
  refine (probEvent_bind_le_probEvent
    (p := fun r => badEnv P msg hasOPK (env.openNext r) = true)
    fun r _ hr => by simp [probEvent_pure, hr]).trans ?_
  have hinit : (uakeInitiator P msg hasOPK).T.init tk = (recipient P hasOPK).init tk := rfl
  rw [hinit]
  refine (probEvent_bind_le_of_forall_le (ε := Pr[ fun kp =>
    kp.1 ∈ keySet P msg hasOPK env | P.pqkem.keygen]) fun opk _ => ?_).trans ?_
  · refine probEvent_bind_le_probEvent fun kp _ hkp =>
      le_antisymm (probEvent_bind_le_of_forall_le fun bd hbd => ?_) zero_le
    erw [probEvent_pure]
    split_ifs with hb
    · exfalso
      refine hkp ?_
      have hmem := mem_keySet_of_badEnv_openNext P msg hasOPK env hbad _ bd hb
      simp only [publish, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
        exists_prop] at hbd
      obtain ⟨_, _, rfl⟩ := hbd
      exact hmem
    · exact le_rfl
  · exact (probEvent_fst_mem_finset_le _ _ ε hpk).trans
      (by gcongr; exact_mod_cast keySet_card_le P msg hasOPK env)

/-- The potential bound for the UAKE oracle, for any budget predicate that holds exactly at
`openT`. -/
theorem probEvent_badEnv_le [DecidableEq PQPK] (tk : RecipientIdentity F G SPK SSK S)
    (ε : ℝ≥0∞) (hpk : ∀ pk, Pr[= pk | Prod.fst <$> P.pqkem.keygen] ≤ ε)
    {p : (unifSpec + oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain → Prop}
    {_ : DecidablePred p} (hp : ∀ t, p t ↔ t = Sum.inr .openT) {α : Type}
    (oa : OracleComp (unifSpec + oracleSpec K (Message G PQPK CT S C IdC IdK)) α) (b : ℕ)
    (hb : oa.IsQueryBoundP p b)
    (env : Env (uakeInitiator P msg hasOPK)) (h : env.SessionsStarted) :
    Pr[ fun z => badEnv P msg hasOPK z.2 = true |
        (simulateQ (oracle P msg hasOPK tk) oa).run env] ≤
      (if badEnv P msg hasOPK env then 1 else 0) +
        ε * ((b * (env.tSessions.length + b) : ℕ) : ℝ≥0∞) :=
  probEvent_simulateQ_bad_le (oracle P msg hasOPK tk) p
    (badEnv P msg hasOPK) (fun env => env.tSessions.length) Env.SessionsStarted ε
    (fun t env h => oracle_inv P msg hasOPK tk t env h)
    (fun t env ht h => oracle_free P msg hasOPK tk t (fun e => ht ((hp t).2 e)) env h)
    (fun t env ht _ => oracleImpl_openT_count _ tk t ((hp t).1 ht) env)
    (fun t env ht _ hbad => oracle_hit P msg hasOPK tk ε hpk t ((hp t).1 ht) env hbad)
    oa b hb env h

/-- Hop 4: the KEM-key guessing bound. It carries `[SampleableType K]` only so that its
signature matches `Protocols.Models.PQXDH.pqpkGuessedProb_le`, which delegates to it. -/
theorem pqpkGuessedProb_le_bound [DecidableEq PQPK] [SampleableType K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εpk : ℝ)
    (hpk : ∀ pk : PQPK, (Pr[= pk | Prod.fst <$> P.pqkem.keygen]).toReal ≤ εpk) :
    pqpkGuessedProb P msg hasOPK A ≤ (q : ℝ) ^ 2 * εpk := by
  have hε0 : 0 ≤ εpk := nonneg_of_probOutput_le _ hpk
  have hpk' : ∀ pk, Pr[= pk | Prod.fst <$> P.pqkem.keygen] ≤ ENNReal.ofReal εpk := fun pk =>
    (ENNReal.le_ofReal_iff_toReal_le probOutput_ne_top hε0).2 (hpk pk)
  have key : Pr[= true | pqpkGuessedExp P msg hasOPK A] ≤
      ENNReal.ofReal εpk * ((q * q : ℕ) : ℝ≥0∞) := by
    rw [← probEvent_eq_eq_probOutput]
    simp only [pqpkGuessedExp, challengePhase, bind_assoc]
    refine probEvent_bind_le_of_forall_le fun ukt _ => ?_
    have hinit : (uakeInitiator P msg hasOPK).U.init ukt.1 = pure (.waitForMsg (.inl ukt.1)) :=
      rfl
    simp only [challengeSession, bind_assoc, hinit, pure_bind, Party.InitResult.opening,
      Party.InitResult.state, recordOpt]
    refine (probEvent_bind_le_probEvent (p := fun z => badEnv P msg hasOPK z.2 = true)
      fun z _ hz => le_antisymm (probEvent_bind_le_of_forall_le fun k0 _ => ?_) zero_le).trans ?_
    · have hk : pqpkGuessed P msg hasOPK
          ⟨k0.join, z.2.challenge.transcript, z.2.tSessions.map (·.transcript)⟩ =
            badEnv P msg hasOPK z.2 := rfl
      simp [hk, hz]
    · refine (probEvent_badEnv_le P msg hasOPK ukt.2 _ hpk' ?_ _ q (hq.1 _ _) _ ?_).trans ?_
      · intro t
        rcases t with n | op
        · simp
        · cases op <;> simp
      · intro s hs
        simp at hs
      · simp [badEnv, envResult, pqpkGuessed, oracleBundles, challengeBundle, transcriptBundle]
  have hfin : ENNReal.ofReal εpk * ((q * q : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  calc pqpkGuessedProb P msg hasOPK A
      ≤ (ENNReal.ofReal εpk * ((q * q : ℕ) : ℝ≥0∞)).toReal := ENNReal.toReal_mono hfin key
    _ = (q : ℝ) ^ 2 * εpk := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε0, ENNReal.toReal_natCast]
      push_cast
      ring

end Model

end Protocols.Models.PQXDH.KeyGuessing
