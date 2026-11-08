/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Defs

/-!
# Facts about the UAKE oracle for any scheme

The UAKE oracle `oracleImpl` keeps an environment `Env` with a clock and the list of T sessions.
This file states, for any scheme over `ProbComp`:

* `Env.openNext` and `oracleImpl_openT_run`: an `openT` query runs `T.init` and appends one
  session; `oracleImpl_openT_count` counts it.
* `Env.SessionsStarted`: every T session has a nonempty transcript whose first entry is stamped
  strictly before the clock. `Env.sessionsStarted_set_extend` and
  `Env.sessionsStarted_clock_mono` show that extending a session's transcript and advancing the
  clock keep it.

The lemma statements and proofs in this file are AI-written.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

variable {K UK TK W : Type} {proto : Scheme ProbComp K UK TK W}

/-- The environment after `openT` received the init result `r`. -/
def Env.openNext (env : Env proto) (r : Party.InitResult proto.T.State W) : Env proto :=
  { env with
    clock := (recordOpt ⟨[]⟩ r.opening env.clock).2
    tSessions := env.tSessions ++
      [⟨r.state, (recordOpt ⟨[]⟩ r.opening env.clock).1, none, false⟩] }

/-- An `openT` query runs `T.init` and appends one session. -/
theorem oracleImpl_openT_run (lift : ProbCompLift ProbComp) (tk : TK) (env : Env proto) :
    (oracleImpl lift proto tk (Sum.inr .openT)).run env =
      (proto.T.init tk >>= fun r =>
        pure ((env.tSessions.length, r.opening), env.openNext r) :
        ProbComp ((unifSpec + oracleSpec K W).Range (Sum.inr .openT) × Env proto)) := by
  simp [oracleImpl, opImpl, Env.openNext]

/-- An `openT` query adds exactly one session. -/
theorem oracleImpl_openT_count (lift : ProbCompLift ProbComp) (tk : TK) (t)
    (ht : t = Sum.inr .openT) (env : Env proto) :
    ∀ z ∈ support ((oracleImpl lift proto tk t).run env),
      z.2.tSessions.length = env.tSessions.length + 1 := by
  subst ht
  intro z hz
  rw [oracleImpl_openT_run, mem_support_bind_iff] at hz
  obtain ⟨r, -, hz⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp [Env.openNext]

/-- Every T session's transcript is nonempty and starts strictly before the clock. -/
def Env.SessionsStarted (env : Env proto) : Prop :=
  ∀ s ∈ env.tSessions, ∃ e es, s.transcript.entries = e :: es ∧ e.2 < env.clock

/-- `SessionsStarted` survives replacing session `sid` by a session whose transcript extends the
old one, while the clock does not decrease. -/
theorem Env.sessionsStarted_set_extend (env : Env proto) (h : env.SessionsStarted)
    {sid : ℕ} {t : TSession proto} (hs : env.tSessions[sid]? = some t)
    (t' : TSession proto) (ext : List (W × ℕ))
    (hext : t'.transcript.entries = t.transcript.entries ++ ext) (c : ℕ) (hc : env.clock ≤ c)
    (ch : Session proto.U.State W) (d : Bool) :
    Env.SessionsStarted (⟨c, ch, d, env.tSessions.set sid t'⟩ : Env proto) := by
  intro s hs'
  rcases List.mem_or_eq_of_mem_set hs' with hs' | rfl
  · obtain ⟨e, es, he, hlt⟩ := h s hs'
    exact ⟨e, es, he, by simp only; omega⟩
  · obtain ⟨e, es, he, hlt⟩ := h t (List.mem_of_getElem? hs)
    exact ⟨e, es ++ ext, by rw [hext, he]; rfl, by simp only; omega⟩

/-- `SessionsStarted` survives a non-decreasing clock when the sessions are unchanged. -/
theorem Env.sessionsStarted_clock_mono (env : Env proto) (h : env.SessionsStarted)
    (c : ℕ) (hc : env.clock ≤ c) (ch : Session proto.U.State W) (d : Bool) :
    Env.SessionsStarted (⟨c, ch, d, env.tSessions⟩ : Env proto) := by
  intro s hs
  obtain ⟨e, es, he, hlt⟩ := h s hs
  exact ⟨e, es, he, by simp only; omega⟩

end AKE.UAKE
