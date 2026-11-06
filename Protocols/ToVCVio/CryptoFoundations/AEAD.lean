/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open OracleSpec OracleComp

universe u

namespace AEAD

structure Scheme (m : Type → Type u) [Monad m] (Msg Key AD C : Type) where
  encrypt : Key → AD → Msg → m C
  decrypt : Key → AD → C → Option Msg

def withUnif {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl (unifSpec + spec) (StateT σ ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget (StateT σ ProbComp) + impl

variable {Msg Key AD C : Type} [DecidableEq Msg] [SampleableType Key]
  [DecidableEq AD] [DecidableEq C]

def CorrectExp (aead : Scheme ProbComp Msg Key AD C) (msg : Msg) (ad : AD) : ProbComp Bool := do
  let k ← $ᵗ Key
  let c ← aead.encrypt k ad msg
  pure (decide (aead.decrypt k ad c = some msg))

def PerfectlyCorrect (aead : Scheme ProbComp Msg Key AD C) : Prop :=
  ∀ msg ad, Pr[= true | CorrectExp aead msg ad] = 1

/-- A challenge query of the IND-CPA game: associated data and two messages with the same
public length `msgLen`. A message type of fixed length uses `msgLen := fun _ => 0`. -/
structure EqualLengthChallenge (AD Msg : Type) (msgLen : Msg → ℕ) where
  ad : AD
  m₀ : Msg
  m₁ : Msg
  sameLength : msgLen m₀ = msgLen m₁

/-- An adversary in the multi-query IND-CPA game with equal-length challenge pairs.

A perfectly correct deterministic encryption algorithm does not satisfy this notion when two
distinct messages `m` and `m'` have the same length: query `(ad, m, m)` and then `(ad, m, m')`
with the same associated data `ad`, and compare the two ciphertexts. Production encrypts each
message with AES-256-CBC under a key and an IV that both come from the message keys
(`rust/protocol/src/triple_ratchet.rs:161`, `rust/protocol/src/session_cipher_legacy.rs:80`), so
production cannot instantiate this notion. No PQXDH theorem uses it. It is kept, repaired, as a
reference. -/
structure IND_CPA_Adversary (_aead : Scheme ProbComp Msg Key AD C) (msgLen : Msg → ℕ) where
  run : OracleComp (unifSpec + (EqualLengthChallenge AD Msg msgLen →ₒ C)) Bool

/-- The IND-CPA challenge oracle encrypts the left or the right message of an equal-length
pair, as the hidden bit `b` says. -/
def cpaImpl (aead : Scheme ProbComp Msg Key AD C) (msgLen : Msg → ℕ) (k : Key) (b : Bool) :
    QueryImpl (unifSpec + (EqualLengthChallenge AD Msg msgLen →ₒ C)) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    fun q : EqualLengthChallenge AD Msg msgLen =>
      (aead.encrypt k q.ad (if b then q.m₁ else q.m₀) : ProbComp C)

def IND_CPA_Game {msgLen : Msg → ℕ} (aead : Scheme ProbComp Msg Key AD C)
    (A : IND_CPA_Adversary aead msgLen) : ProbComp Bool := do
  let k ← $ᵗ Key
  let b ← $ᵗ Bool
  let b' ← simulateQ (cpaImpl aead msgLen k b) A.run
  pure (b' == b)

noncomputable def IND_CPA_Advantage {msgLen : Msg → ℕ} (aead : Scheme ProbComp Msg Key AD C)
    (A : IND_CPA_Adversary aead msgLen) : ℝ :=
  |(Pr[= true | IND_CPA_Game aead A]).toReal - 1 / 2|

def ctxtImpl (aead : Scheme ProbComp Msg Key AD C) (k : Key) :
    QueryImpl ((AD × Msg) →ₒ C) (StateT (List (AD × C)) ProbComp) :=
  fun p => do
    let c ← (aead.encrypt k p.1 p.2 : ProbComp C)
    modify (fun log => log ++ [(p.1, c)])
    pure c

structure INT_CTXT_Adversary (_aead : Scheme ProbComp Msg Key AD C) where
  run : OracleComp (unifSpec + ((AD × Msg) →ₒ C)) (AD × C)

def INT_CTXT_Game (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_Adversary aead) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (forge, log) ← (simulateQ (withUnif (ctxtImpl aead k)) A.run).run []
  pure ((aead.decrypt k forge.1 forge.2).isSome && decide (forge ∉ log))

noncomputable def INT_CTXT_Advantage (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_Adversary aead) : ℝ :=
  (Pr[= true | INT_CTXT_Game aead A]).toReal

def ctxtVfImpl (aead : Scheme ProbComp Msg Key AD C) (k : Key) :
    QueryImpl (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))
      (StateT (List (AD × C) × Bool) ProbComp) :=
  (show QueryImpl ((AD × Msg) →ₒ C) (StateT (List (AD × C) × Bool) ProbComp) from
    fun p => do
      let c ← (aead.encrypt k p.1 p.2 : ProbComp C)
      modify (fun s => (s.1 ++ [(p.1, c)], s.2))
      pure c) +
  (show QueryImpl ((AD × C) →ₒ Bool) (StateT (List (AD × C) × Bool) ProbComp) from
    fun p => do
      let ok := (aead.decrypt k p.1 p.2).isSome
      modify (fun s => (s.1, s.2 || (ok && decide (p ∉ s.1))))
      pure ok)

structure INT_CTXT_VF_Adversary (_aead : Scheme ProbComp Msg Key AD C) where
  run : OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))) Unit

def INT_CTXT_VF_Game (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_VF_Adversary aead) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (_, _, won) ← (simulateQ (withUnif (ctxtVfImpl aead k)) A.run).run ([], false)
  pure won

noncomputable def INT_CTXT_VF_Advantage (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_VF_Adversary aead) : ℝ :=
  (Pr[= true | INT_CTXT_VF_Game aead A]).toReal

def ctxtDecImpl (aead : Scheme ProbComp Msg Key AD C) (k : Key) :
    QueryImpl (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))
      (StateT (List (AD × C) × Bool) ProbComp) :=
  (show QueryImpl ((AD × Msg) →ₒ C) (StateT (List (AD × C) × Bool) ProbComp) from
    fun p => do
      let c ← (aead.encrypt k p.1 p.2 : ProbComp C)
      modify (fun s => (s.1 ++ [(p.1, c)], s.2))
      pure c) +
  (show QueryImpl ((AD × C) →ₒ Option Msg) (StateT (List (AD × C) × Bool) ProbComp) from
    fun p => do
      modify (fun s => (s.1, s.2 || ((aead.decrypt k p.1 p.2).isSome && decide (p ∉ s.1))))
      pure (aead.decrypt k p.1 p.2))

structure INT_CTXT_D_Adversary (_aead : Scheme ProbComp Msg Key AD C) where
  run : OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))) Unit

def INT_CTXT_D_Game (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_D_Adversary aead) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (_, _, won) ← (simulateQ (withUnif (ctxtDecImpl aead k)) A.run).run ([], false)
  pure won

noncomputable def INT_CTXT_D_Advantage (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_D_Adversary aead) : ℝ :=
  (Pr[= true | INT_CTXT_D_Game aead A]).toReal

/-! ## From the plain game to the checking games

`ctxtToVf A` and `ctxtToDec A` run a plain adversary `A` inside the verification and the
decryption game and submit its forgery as one checking query. The checking game then scores
exactly the plain game. -/

/-- Embeds the plain adversary's queries into the verification game's oracles: uniform queries
and encryption queries pass through unchanged. -/
def ctxtToVfImpl : QueryImpl (unifSpec + ((AD × Msg) →ₒ C))
    (OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))))
  | .inl n => liftM (OracleSpec.query
      (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))) (.inl n))
  | .inr x => liftM (OracleSpec.query
      (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))) (.inr (.inl x)))

/-- The verification-game adversary that runs `A` and submits its forgery to the verification
oracle. -/
def ctxtToVf {aead : Scheme ProbComp Msg Key AD C} (A : INT_CTXT_Adversary aead) :
    INT_CTXT_VF_Adversary aead :=
  ⟨do
    let forge ← simulateQ ctxtToVfImpl A.run
    let _ ← liftM (OracleSpec.query
      (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))) (.inr (.inr forge)))
    pure ()⟩

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtToVf_hproj (aead : Scheme ProbComp Msg Key AD C) (k : Key)
    (t : (unifSpec + ((AD × Msg) →ₒ C)).Domain) (s : List (AD × C)) :
    Prod.map id (fun log => (log, false)) <$> ((withUnif (ctxtImpl aead k)) t).run s =
      (((withUnif (ctxtVfImpl aead k)) ∘ₛ ctxtToVfImpl) t).run (s, false) := by
  rcases t with n | x
  · simp [withUnif, ctxtToVfImpl]
  · simp [withUnif, ctxtToVfImpl, ctxtImpl, ctxtVfImpl]

omit [DecidableEq Msg] in
/-- The verification game of `ctxtToVf A` is the plain game of `A`: the run of `A` leaves the
flag `false`, and the final verification query sets it to the plain game's output. -/
theorem INT_CTXT_VF_Game_ctxtToVf (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_Adversary aead) :
    INT_CTXT_VF_Game aead (ctxtToVf A) = INT_CTXT_Game aead A := by
  unfold INT_CTXT_VF_Game INT_CTXT_Game ctxtToVf
  refine bind_congr fun k => ?_
  have h := map_run_simulateQ_eq_of_query_map_eq (withUnif (ctxtImpl aead k))
    ((withUnif (ctxtVfImpl aead k)) ∘ₛ ctxtToVfImpl) (fun log => (log, false))
    (ctxtToVf_hproj aead k) A.run []
  simp only [simulateQ_bind, StateT.run_bind, ← QueryImpl.simulateQ_compose, ← h]
  simp [withUnif, ctxtVfImpl]
  rfl

/-- Embeds the plain adversary's queries into the decryption game's oracles: uniform queries
and encryption queries pass through unchanged. -/
def ctxtToDecImpl : QueryImpl (unifSpec + ((AD × Msg) →ₒ C))
    (OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))))
  | .inl n => liftM (OracleSpec.query
      (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))) (.inl n))
  | .inr x => liftM (OracleSpec.query
      (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))) (.inr (.inl x)))

/-- The decryption-game adversary that runs `A` and submits its forgery to the decryption
oracle. -/
def ctxtToDec {aead : Scheme ProbComp Msg Key AD C} (A : INT_CTXT_Adversary aead) :
    INT_CTXT_D_Adversary aead :=
  ⟨do
    let forge ← simulateQ ctxtToDecImpl A.run
    let _ ← liftM (OracleSpec.query
      (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))) (.inr (.inr forge)))
    pure ()⟩

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtToDec_hproj (aead : Scheme ProbComp Msg Key AD C) (k : Key)
    (t : (unifSpec + ((AD × Msg) →ₒ C)).Domain) (s : List (AD × C)) :
    Prod.map id (fun log => (log, false)) <$> ((withUnif (ctxtImpl aead k)) t).run s =
      (((withUnif (ctxtDecImpl aead k)) ∘ₛ ctxtToDecImpl) t).run (s, false) := by
  rcases t with n | x
  · simp [withUnif, ctxtToDecImpl]
  · simp [withUnif, ctxtToDecImpl, ctxtImpl, ctxtDecImpl]

omit [DecidableEq Msg] in
/-- The decryption game of `ctxtToDec A` is the plain game of `A`, as for
`INT_CTXT_VF_Game_ctxtToVf`. -/
theorem INT_CTXT_D_Game_ctxtToDec (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_Adversary aead) :
    INT_CTXT_D_Game aead (ctxtToDec A) = INT_CTXT_Game aead A := by
  unfold INT_CTXT_D_Game INT_CTXT_Game ctxtToDec
  refine bind_congr fun k => ?_
  have h := map_run_simulateQ_eq_of_query_map_eq (withUnif (ctxtImpl aead k))
    ((withUnif (ctxtDecImpl aead k)) ∘ₛ ctxtToDecImpl) (fun log => (log, false))
    (ctxtToDec_hproj aead k) A.run []
  simp only [simulateQ_bind, StateT.run_bind, ← QueryImpl.simulateQ_compose, ← h]
  simp [withUnif, ctxtDecImpl]
  rfl

omit [DecidableEq Msg] in
/-- `ctxtToVf A` has exactly the plain advantage of `A`. -/
theorem INT_CTXT_VF_Advantage_ctxtToVf
    (aead : Scheme ProbComp Msg Key AD C) (A : INT_CTXT_Adversary aead) :
    INT_CTXT_VF_Advantage aead (ctxtToVf A) = INT_CTXT_Advantage aead A := by
  rw [INT_CTXT_VF_Advantage, INT_CTXT_VF_Game_ctxtToVf, INT_CTXT_Advantage]

omit [DecidableEq Msg] in
/-- `ctxtToDec A` has exactly the plain advantage of `A`. -/
theorem INT_CTXT_D_Advantage_ctxtToDec
    (aead : Scheme ProbComp Msg Key AD C) (A : INT_CTXT_Adversary aead) :
    INT_CTXT_D_Advantage aead (ctxtToDec A) = INT_CTXT_Advantage aead A := by
  rw [INT_CTXT_D_Advantage, INT_CTXT_D_Game_ctxtToDec, INT_CTXT_Advantage]

/-! ## Query bounds of the reductions

These lemmas count oracle queries only. The running time of the reductions and their uniform
queries are not counted here; cost accounting is deferred to #41. -/

/-- A query bound transfers through a stateless handler that answers each counted query with
at most one counted query and every other query with none. -/
private theorem isQueryBoundP_simulateQ_of_step {ι ι' : Type} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} {p : ι → Prop} [DecidablePred p] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')} {α : Type} {oa : OracleComp spec α} {n : ℕ}
    (h : oa.IsQueryBoundP p n) (hstep : ∀ t, (impl t).IsQueryBoundP q (if p t then 1 else 0)) :
    (simulateQ impl oa).IsQueryBoundP q n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_query_bind]
    refine (isQueryBoundP_bind (hstep t) fun x _ => ih x (h.2 x)).mono ?_
    rcases h.1 with h1 | h1 <;> split_ifs <;> omega

omit [DecidableEq Msg] [SampleableType Key] [DecidableEq AD] [DecidableEq C] in
/-- `ctxtToVf A` makes as many encryption queries as `A`. -/
theorem ctxtToVf_encBound {aead : Scheme ProbComp Msg Key AD C}
    (A : INT_CTXT_Adversary aead) {e : ℕ}
    (he : A.run.IsQueryBoundP (· matches Sum.inr _) e) :
    (ctxtToVf A).run.IsQueryBoundP (· matches Sum.inr (Sum.inl _)) e := by
  have h := isQueryBoundP_bind (n := e) (m := 0)
    (isQueryBoundP_simulateQ_of_step (impl := ctxtToVfImpl)
      (q := (· matches Sum.inr (Sum.inl _))) he fun t => by
        rcases t with n | x <;> exact (isQueryBoundP_query_iff _ _ _).2 (by simp))
    (ob := fun forge => (do
      let _ ← liftM (OracleSpec.query
        (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))) (.inr (.inr forge)))
      pure () : OracleComp _ Unit))
    fun forge _ => (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun _ => trivial⟩
  simpa [ctxtToVf] using h

omit [DecidableEq Msg] [SampleableType Key] [DecidableEq AD] [DecidableEq C] in
/-- `ctxtToVf A` makes one verification query. -/
theorem ctxtToVf_vfBound {aead : Scheme ProbComp Msg Key AD C}
    (A : INT_CTXT_Adversary aead) :
    (ctxtToVf A).run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) 1 := by
  have h := isQueryBoundP_bind (n := 0) (m := 1)
    (isQueryBoundP_simulateQ_of_step (impl := ctxtToVfImpl)
      (q := (· matches Sum.inr (Sum.inr _))) (isQueryBoundP_false A.run 0) fun t => by
        rcases t with n | x <;> exact (isQueryBoundP_query_iff _ _ _).2 (by simp))
    (ob := fun forge => (do
      let _ ← liftM (OracleSpec.query
        (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))) (.inr (.inr forge)))
      pure () : OracleComp _ Unit))
    fun forge _ => (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun _ => trivial⟩
  simpa [ctxtToVf] using h

omit [DecidableEq Msg] [SampleableType Key] [DecidableEq AD] [DecidableEq C] in
/-- `ctxtToDec A` makes as many encryption queries as `A`. -/
theorem ctxtToDec_encBound {aead : Scheme ProbComp Msg Key AD C}
    (A : INT_CTXT_Adversary aead) {e : ℕ}
    (he : A.run.IsQueryBoundP (· matches Sum.inr _) e) :
    (ctxtToDec A).run.IsQueryBoundP (· matches Sum.inr (Sum.inl _)) e := by
  have h := isQueryBoundP_bind (n := e) (m := 0)
    (isQueryBoundP_simulateQ_of_step (impl := ctxtToDecImpl)
      (q := (· matches Sum.inr (Sum.inl _))) he fun t => by
        rcases t with n | x <;> exact (isQueryBoundP_query_iff _ _ _).2 (by simp))
    (ob := fun forge => (do
      let _ ← liftM (OracleSpec.query
        (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))) (.inr (.inr forge)))
      pure () : OracleComp _ Unit))
    fun forge _ => (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun _ => trivial⟩
  simpa [ctxtToDec] using h

omit [DecidableEq Msg] [SampleableType Key] [DecidableEq AD] [DecidableEq C] in
/-- `ctxtToDec A` makes one decryption query. -/
theorem ctxtToDec_decBound {aead : Scheme ProbComp Msg Key AD C}
    (A : INT_CTXT_Adversary aead) :
    (ctxtToDec A).run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) 1 := by
  have h := isQueryBoundP_bind (n := 0) (m := 1)
    (isQueryBoundP_simulateQ_of_step (impl := ctxtToDecImpl)
      (q := (· matches Sum.inr (Sum.inr _))) (isQueryBoundP_false A.run 0) fun t => by
        rcases t with n | x <;> exact (isQueryBoundP_query_iff _ _ _).2 (by simp))
    (ob := fun forge => (do
      let _ ← liftM (OracleSpec.query
        (spec := unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))) (.inr (.inr forge)))
      pure () : OracleComp _ Unit))
    fun forge _ => (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun _ => trivial⟩
  simpa [ctxtToDec] using h

/-! ## The four lemmas -/

omit [DecidableEq Msg] in
/-- Plain INT-CTXT is no harder than the verification-oracle variant: `ctxtToVf A` runs `A` and
submits its forgery to the verification oracle, and the two advantages are equal
(`INT_CTXT_VF_Advantage_ctxtToVf`). No PQXDH theorem uses this lemma. -/
theorem INT_CTXT_Advantage_le_INT_CTXT_VF_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (A : INT_CTXT_Adversary aead) :
    INT_CTXT_Advantage aead A ≤ INT_CTXT_VF_Advantage aead (ctxtToVf A) :=
  (INT_CTXT_VF_Advantage_ctxtToVf aead A).ge

/-- The verification-oracle variant loses at most the query bound `v`: `A` guesses which of
`B`'s verification queries is the first fresh valid one and outputs it. No PQXDH theorem uses
this lemma. A proof is a hybrid over the `v` verification queries, using `hcorrect` to answer the
honest ones. -/
theorem INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (hcorrect : PerfectlyCorrect aead)
    (B : INT_CTXT_VF_Adversary aead) (v : ℕ)
    (hv : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) v) :
    ∃ A : INT_CTXT_Adversary aead,
      INT_CTXT_VF_Advantage aead B ≤ (v : ℝ) * INT_CTXT_Advantage aead A := by
  sorry

omit [DecidableEq Msg] in
/-- Plain INT-CTXT is no harder than the decryption-oracle variant: `ctxtToDec A` runs `A` and
submits its forgery to the decryption oracle, and the two advantages are equal
(`INT_CTXT_D_Advantage_ctxtToDec`). No PQXDH theorem uses this lemma. The PQXDH security
theorems assume a bound on `INT_CTXT_D_Advantage` directly. -/
theorem INT_CTXT_Advantage_le_INT_CTXT_D_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (A : INT_CTXT_Adversary aead) :
    INT_CTXT_Advantage aead A ≤ INT_CTXT_D_Advantage aead (ctxtToDec A) :=
  (INT_CTXT_D_Advantage_ctxtToDec aead A).ge

/-- The decryption-oracle variant loses at most the query bound `v`. No PQXDH theorem uses this
lemma. A proof follows `INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage`. -/
theorem INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (hcorrect : PerfectlyCorrect aead)
    (B : INT_CTXT_D_Adversary aead) (v : ℕ)
    (hv : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) v) :
    ∃ A : INT_CTXT_Adversary aead,
      INT_CTXT_D_Advantage aead B ≤ (v : ℝ) * INT_CTXT_Advantage aead A := by
  sorry

end AEAD
