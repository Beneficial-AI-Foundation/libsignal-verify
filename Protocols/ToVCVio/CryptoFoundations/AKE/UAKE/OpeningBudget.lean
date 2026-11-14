/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.OracleInvariants
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Partnering

/-!
# The opening budget of a UAKE adversary

`Adversary.OpensAtMost q` bounds the `openT` queries of each stage of the adversary by `q`: at
most `q` in the challenge stage and at most `q` in the key-distinguishing stage. It is the budget
of PQXDH-model and has the same body as `Adversary.OpensAtMostPerPhase` (`Partnering.lean`).

The budget is per stage, so the two stages together may open `2 * q` sessions. This file proves
that the experiment allows no more. At most `q` sessions are open when the challenge stage ends
(`Adversary.OpensAtMost.challengeSession_openCount_le`). At most `2 * q` are open when the
key-distinguishing stage ends, which `finalize` and `finalizePartnered` run from the environment
of the challenge stage (`Adversary.OpensAtMost.openCount_le_two_mul`). `Exp` and `PartneredExp`
return early, with no key-distinguishing stage, when the challenge accepts without a partner, and
the first bound covers that branch. The fixtures in `ProtocolsTest` show that `2 * q` is reached
at `q = 1`.

The budget counts `openT` queries only. It is no resource bound on the adversary (#41).
-/

open OracleSpec OracleComp

namespace AKE.UAKE

variable {K UK TK W : Type}

/-- The adversary opens at most `q` sessions of T in its challenge stage and at most `q` in its
key-distinguishing stage, so at most `2 * q` in all
(`Adversary.OpensAtMost.openCount_le_two_mul`). -/
def Adversary.OpensAtMost {proto : Scheme ProbComp K UK TK W} (A : Adversary proto) (q : ℕ) :
    Prop :=
  (∀ uk w, (A.challenge uk w).IsQueryBoundP (· matches Sum.inr .openT) q) ∧
    (∀ st k, (A.post st k).IsQueryBoundP (· matches Sum.inr .openT) q)

/-- `OpensAtMost` and `OpensAtMostPerPhase` are the same budget. -/
theorem Adversary.opensAtMost_iff_opensAtMostPerPhase {proto : Scheme ProbComp K UK TK W}
    (A : Adversary proto) (q : ℕ) : A.OpensAtMost q ↔ A.OpensAtMostPerPhase q := Iff.rfl

variable {proto : Scheme ProbComp K UK TK W}

/-- A query other than `openT` leaves the number of T sessions unchanged. -/
theorem oracleImpl_openCount_of_not_openT (lift : ProbCompLift ProbComp) (tk : TK)
    (t : (unifSpec + oracleSpec K W).Domain) (ht : ¬ (t matches Sum.inr .openT))
    (env : Env proto) :
    ∀ z ∈ support ((oracleImpl lift proto tk t).run env),
      z.2.tSessions.length = env.tSessions.length := by
  intro z hz
  rcases t with n | op
  · simp only [oracleImpl, HasQuery.toQueryImpl_apply, HasQuery.instOfMonadLift_query,
      QueryImpl.add_apply_inl, StateT.run_monadLift, monadLift_self, bind_pure_comp,
      support_map] at hz
    obtain ⟨a, -, rfl⟩ := hz
    rfl
  · cases op with
    | openT => exact absurd rfl ht
    | revealT sid =>
      simp only [oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hs,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        rfl
      · rcases hk : t.key with _ | key
        · simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
            hs, hk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          rfl
        · simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
            hs, hk, StateT.run_map, StateT.run_set, map_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          simp
    | stepT sid w =>
      simp only [oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get, hs,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        rfl
      · rcases hk : t.key with _ | key
        · simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get,
            hs, hk, StateT.run_monadLift, monadLift_self, bind_map_left] at hz
          obtain ⟨res, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
          cases res with
          | reject =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            rfl
          | acceptAndSend st' w' done =>
            cases done
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_map, StateT.run_set,
                map_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz
              simp
            · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
                bind_pure_comp, StateT.run_map, StateT.run_set, map_pure, Functor.map_map,
                support_map, Set.mem_image] at hz
              obtain ⟨y, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
              simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
              subst hz
              simp
          | complete st' =>
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
              StateT.run_map, StateT.run_set, map_pure, Functor.map_map, support_map,
              Set.mem_image] at hz
            obtain ⟨y, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
            simp only [pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
            subst hz
            simp
        · simp only [bind_pure_comp, pure_bind, StateT.run_bind, StateT.run_get,
            hs, hk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          rfl
    | stepChallenge w =>
      simp only [oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      by_cases hd : env.challengeDone = true
      · simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hd,
          ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        rfl
      · simp only [bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind, hd,
          Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
          bind_map_left] at hz
        obtain ⟨res, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
        cases res with
        | reject =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          rfl
        | acceptAndSend st' w' done =>
          simp only [StateT.run_map, StateT.run_set, map_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          rfl
        | complete st' =>
          simp only [StateT.run_map, StateT.run_set, map_pure, support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          rfl

/-- A computation with at most `n` `openT` queries, simulated with the UAKE oracle, opens at most
`n` sessions. -/
theorem simulateQ_oracleImpl_openCount_le (lift : ProbCompLift ProbComp) (tk : TK) {α : Type}
    {oa : OracleComp (unifSpec + oracleSpec K W) α} {n : ℕ}
    (h : oa.IsQueryBoundP (· matches Sum.inr .openT) n) (env : Env proto) :
    ∀ z ∈ support ((simulateQ (oracleImpl lift proto tk) oa).run env),
      z.2.tSessions.length ≤ env.tSessions.length + n := by
  refine IsQueryBoundP.cost_le_of_mem_support_run_simulateQ
    (fun env : Env proto => env.tSessions.length) ?_ ?_ h env
  · intro t ht s z hz
    have hopen : t = Sum.inr .openT := by
      revert ht; clear hz z; rcases t with _ | (_ | _ | _ | _) <;> simp
    exact (oracleImpl_openT_count lift tk t hopen s z hz).le
  · intro t ht s z hz
    exact (oracleImpl_openCount_of_not_openT lift tk t
      (by revert ht; clear hz z; rcases t with _ | (_ | _ | _ | _) <;> simp) s z hz).le

/-- At most `q` sessions are open when the challenge stage ends. -/
theorem Adversary.OpensAtMost.challengeSession_openCount_le {A : Adversary proto} {q : ℕ}
    (hq : A.OpensAtMost q) (lift : ProbCompLift ProbComp) (uk : UK) (tk : TK) :
    ∀ z ∈ support (challengeSession lift A uk tk), z.2.2.1.tSessions.length ≤ q := by
  intro z hz
  simp only [challengeSession, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨u0, -, ⟨st, env⟩, hrun, k0, -, rfl⟩ := hz
  have := simulateQ_oracleImpl_openCount_le lift tk (hq.1 uk u0.opening) _ (st, env) hrun
  simpa using this

/-- The key-distinguishing stage, run from an environment with at most `q` sessions, ends with at
most `2 * q`. -/
theorem Adversary.OpensAtMost.post_openCount_le {A : Adversary proto} {q : ℕ}
    (hq : A.OpensAtMost q) (lift : ProbCompLift ProbComp) (tk : TK) (aSt : A.State)
    (k : Option K) (env : Env proto) (henv : env.tSessions.length ≤ q) :
    ∀ y ∈ support ((simulateQ (oracleImpl lift proto tk) (A.post aSt k)).run env),
      y.2.tSessions.length ≤ 2 * q := by
  intro y hy
  have := simulateQ_oracleImpl_openCount_le lift tk (hq.2 aSt k) env y hy
  omega

/-- The composed opening budget: after the challenge stage and the key-distinguishing stage that
`finalize` and `finalizePartnered` run from its environment, at most `2 * q` sessions are open. -/
theorem Adversary.OpensAtMost.openCount_le_two_mul {A : Adversary proto} {q : ℕ}
    (hq : A.OpensAtMost q) (lift : ProbCompLift ProbComp) (uk : UK) (tk : TK) :
    ∀ z ∈ support (challengeSession lift A uk tk), ∀ k : Option K,
      ∀ y ∈ support ((simulateQ (oracleImpl lift proto tk) (A.post z.2.1 k)).run
          { z.2.2.1 with challengeDone := true }),
        y.2.tSessions.length ≤ 2 * q := by
  intro z hz k y hy
  exact hq.post_openCount_le lift tk z.2.1 k { z.2.2.1 with challengeDone := true }
    (hq.challengeSession_openCount_le lift uk tk z hz) y hy

end AKE.UAKE
