/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# AEAD security notions

An AEAD scheme (`Scheme`) with its correctness condition (`PerfectlyCorrect`), the multi-query
IND-CPA game, and three ciphertext-integrity games: the plain game (`INT_CTXT_Game`, the
adversary outputs one forgery), the verification game (`INT_CTXT_VF_Game`, the adversary queries
a verification oracle) and the decryption game (`INT_CTXT_D_Game`, it queries a decryption
oracle). Four lemmas relate the integrity games. The PQXDH model's security theorems assume a
bound on `INT_CTXT_D_Advantage` directly and use none of the four lemmas.

The IND-CPA challenge takes equal-length message pairs (`EqualLengthChallenge`, #31). IND-CPA
is a reference notion: production's deterministic message encryption cannot instantiate it (see
`IND_CPA_Adversary`).

Each integrity lemma bounds an explicit reduction: `ctxtToVf`, `ctxtToDec`, `vfToCtxt` or
`decToCtxt` (#33). Further lemmas bound the reductions' encryption and checking queries. The
reductions' running time and uniform queries are not counted; cost accounting is left to #41.
The two multiplicative lemmas take `fallback : AD × C`, the reduction's output when it captures
nothing (#32). So they have no instance when `AD × C` is empty.

secure-messaging's one-time IND-CCA notion (secure-messaging `8369ee7`,
`SecureMessaging/AEAD/Defs.lean`: `OneTimeCCAAdversary`, `aeadSecurityImpl`, `securityExp`)
refuses decryption of the challenge pair. It is the planned route for a later instantiation. An
adapter must keep the scheme's key generation (`AEADScheme.keygen` there) and assume
`PerfectlyCorrect`.
-/

open OracleSpec OracleComp
open scoped ENNReal

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
distinct messages `m` and `m'` have the same length: for some associated data `ad`, query
`(ad, m, m)` and then `(ad, m, m')`, and compare the two ciphertexts. Production encrypts each
message with AES-256-CBC under a key and an IV that both come from the message keys
(`rust/protocol/src/triple_ratchet.rs:161`, `rust/protocol/src/session_cipher_legacy.rs:80`), so
production cannot instantiate this reference notion. No PQXDH theorem uses it. -/
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
/-- An upper bound `e` on the encryption queries of `A` is also an upper bound on the encryption
queries of `ctxtToVf A`. -/
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
/-- `ctxtToVf A` makes at most one verification query. -/
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
/-- An upper bound `e` on the encryption queries of `A` is also an upper bound on the encryption
queries of `ctxtToDec A`. -/
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
/-- `ctxtToDec A` makes at most one decryption query. -/
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

/-! ## From a checking game to the plain game: guessing reductions

`vfToCtxt fallback v B` and `decToCtxt fallback v B` draw an index `j` uniformly from
`[0, v - 1]` and run `B`, answering its queries without the key. Encryption queries are
forwarded and logged until the reduction captures `B`'s checking query number `j` (counted from
0); after the capture they are answered with `fallback.2`, so the plain game's log stops
growing. Uniform queries are forwarded at every stage. Checking queries are answered from the
log. For a perfectly correct scheme these answers agree with the real oracle as long as nothing
is captured and no fresh valid pair has been queried. After a capture the log stops growing, so
later answers can differ from the real oracle. The bound does not depend on them. The reduction
outputs the captured pair, or `fallback` if there is none. -/

/-- The state of a guessing reduction: its copy `log` of the encryption log, the number `seen`
of checking queries so far, and the captured checking query `guess`. -/
structure GuessState (Entry Out : Type) where
  log : List Entry
  seen : ℕ
  guess : Option Out

/-- The handler of `vfToCtxtAt fallback j`: it forwards uniform queries, forwards and logs
encryption queries until the capture, captures verification query number `j`, and answers
verification queries from its log. -/
def vfGuessImpl (fallback : AD × C) (j : ℕ) :
    QueryImpl (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool)))
      (StateT (GuessState (AD × C) (AD × C)) (OracleComp (unifSpec + ((AD × Msg) →ₒ C))))
  | .inl n => liftM (OracleSpec.query (spec := unifSpec + ((AD × Msg) →ₒ C)) (.inl n))
  | .inr (.inl x) => do
      let s ← get
      match s.guess with
      | none =>
        let c : C ← liftM (OracleSpec.query (spec := unifSpec + ((AD × Msg) →ₒ C)) (.inr x))
        set { s with log := s.log ++ [(x.1, c)] }
        pure c
      | some _ => pure fallback.2
  | .inr (.inr p) => do
      let s ← get
      set { s with seen := s.seen + 1, guess := s.guess.or (if s.seen = j then some p else none) }
      pure (decide (p ∈ s.log))

/-- The plain adversary that runs `B` with `vfGuessImpl fallback j` and outputs the captured
pair, or `fallback` if `B` makes at most `j` verification queries. -/
def vfToCtxtAt {aead : Scheme ProbComp Msg Key AD C} (fallback : AD × C) (j : ℕ)
    (B : INT_CTXT_VF_Adversary aead) : INT_CTXT_Adversary aead :=
  ⟨(fun r => r.2.guess.getD fallback) <$>
    (simulateQ (vfGuessImpl fallback j) B.run).run ⟨[], 0, none⟩⟩

/-- The plain adversary that draws an index `i` uniformly from `[0, v - 1]` and runs
`vfToCtxtAt fallback i B`. -/
def vfToCtxt {aead : Scheme ProbComp Msg Key AD C} (fallback : AD × C) (v : ℕ)
    (B : INT_CTXT_VF_Adversary aead) : INT_CTXT_Adversary aead :=
  ⟨do
    let i : Fin (v - 1 + 1) ←
      liftM (OracleSpec.query (spec := unifSpec + ((AD × Msg) →ₒ C)) (.inl (v - 1)))
    (vfToCtxtAt fallback i.val B).run⟩

/-- One step of `vfGuessImpl` run inside the plain game: the state pairs the reduction's state
with the plain game's encryption log. The final map reorders `((answer, state), log)` into
`(answer, state, log)`; it is the inverse of the reordering in
`simulateQ_StateT_StateT_compose`. -/
private def vfGuessGameImpl (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C) (j : ℕ)
    (k : Key) : QueryImpl (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool)))
      (StateT (GuessState (AD × C) (AD × C) × List (AD × C)) ProbComp) := fun q =>
  StateT.mk fun sc => (fun r => (r.1.1, r.1.2, r.2)) <$>
    (simulateQ (withUnif (ctxtImpl aead k)) ((vfGuessImpl fallback j q).run sc.1)).run sc.2

omit [DecidableEq Msg] [SampleableType Key] in
private theorem vfGuessGameImpl_unif (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C)
    (j : ℕ) (k : Key) (n : ℕ) (g : GuessState (AD × C) (AD × C)) (L : List (AD × C)) :
    ((vfGuessGameImpl aead fallback j k) (.inl n)).run (g, L) =
      (fun u => (u, (g, L))) <$> (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) := by
  simp [vfGuessGameImpl, vfGuessImpl, withUnif]

omit [DecidableEq Msg] [SampleableType Key] in
private theorem vfGuessGameImpl_enc_none (aead : Scheme ProbComp Msg Key AD C)
    (fallback : AD × C) (j : ℕ) (k : Key) (x : AD × Msg) (g : GuessState (AD × C) (AD × C))
    (hg : g.guess = none) (L : List (AD × C)) :
    ((vfGuessGameImpl aead fallback j k) (.inr (.inl x))).run (g, L) =
      (fun c => (c, ({ g with log := g.log ++ [(x.1, c)] }, L ++ [(x.1, c)]))) <$>
        aead.encrypt k x.1 x.2 := by
  simp [vfGuessGameImpl, vfGuessImpl, withUnif, ctxtImpl, hg]

omit [DecidableEq Msg] [SampleableType Key] in
private theorem vfGuessGameImpl_enc_some (aead : Scheme ProbComp Msg Key AD C)
    (fallback : AD × C) (j : ℕ) (k : Key) (x : AD × Msg) (g : GuessState (AD × C) (AD × C))
    (p : AD × C) (hg : g.guess = some p) (L : List (AD × C)) :
    ((vfGuessGameImpl aead fallback j k) (.inr (.inl x))).run (g, L) =
      pure (fallback.2, (g, L)) := by
  simp [vfGuessGameImpl, vfGuessImpl, hg]

omit [DecidableEq Msg] [SampleableType Key] in
private theorem vfGuessGameImpl_vf (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C)
    (j : ℕ) (k : Key) (p : AD × C) (g : GuessState (AD × C) (AD × C)) (L : List (AD × C)) :
    ((vfGuessGameImpl aead fallback j k) (.inr (.inr p))).run (g, L) =
      pure (decide (p ∈ g.log),
        (⟨g.log, g.seen + 1, g.guess.or (if g.seen = j then some p else none)⟩, L)) := by
  simp [vfGuessGameImpl, vfGuessImpl]

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtVfImpl_unif (aead : Scheme ProbComp Msg Key AD C) (k : Key) (n : ℕ)
    (s : List (AD × C) × Bool) :
    ((withUnif (ctxtVfImpl aead k)) (.inl n)).run s =
      (fun u => (u, s)) <$> (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) := by
  simp [withUnif]

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtVfImpl_enc (aead : Scheme ProbComp Msg Key AD C) (k : Key) (x : AD × Msg)
    (L : List (AD × C)) (b : Bool) :
    ((withUnif (ctxtVfImpl aead k)) (.inr (.inl x))).run (L, b) =
      (fun c => (c, (L ++ [(x.1, c)], b))) <$> aead.encrypt k x.1 x.2 := by
  simp [withUnif, ctxtVfImpl]

omit [DecidableEq Msg] [SampleableType Key] in
private theorem vfGuessGameImpl_unif' (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C)
    (j : ℕ) (k : Key) (n : ℕ) (g : GuessState (AD × C) (AD × C)) (L : List (AD × C)) :
    ((vfGuessGameImpl aead fallback j k) (.inl n)).run (g, L) =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp
        ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))).Range (.inl n))) >>=
        fun u => pure (u, (g, L)) := by
  rw [vfGuessGameImpl_unif, map_eq_bind_pure_comp]; rfl

omit [DecidableEq Msg] [SampleableType Key] in
private theorem vfGuessGameImpl_enc_none' (aead : Scheme ProbComp Msg Key AD C)
    (fallback : AD × C) (j : ℕ) (k : Key) (x : AD × Msg) (g : GuessState (AD × C) (AD × C))
    (hg : g.guess = none) (L : List (AD × C)) :
    ((vfGuessGameImpl aead fallback j k) (.inr (.inl x))).run (g, L) =
      (@id (ProbComp
          ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))).Range (.inr (.inl x))))
        (aead.encrypt k x.1 x.2)) >>= fun c =>
        pure (c, ({ g with log := g.log ++ [(x.1, @id C c)] }, L ++ [(x.1, @id C c)])) := by
  rw [vfGuessGameImpl_enc_none aead fallback j k x g hg, map_eq_bind_pure_comp]; rfl

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtVfImpl_unif' (aead : Scheme ProbComp Msg Key AD C) (k : Key) (n : ℕ)
    (s : List (AD × C) × Bool) :
    ((withUnif (ctxtVfImpl aead k)) (.inl n)).run s =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp
        ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))).Range (.inl n))) >>=
        fun u => pure (u, s) := by
  rw [ctxtVfImpl_unif, map_eq_bind_pure_comp]; rfl

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtVfImpl_enc' (aead : Scheme ProbComp Msg Key AD C) (k : Key) (x : AD × Msg)
    (L : List (AD × C)) (b : Bool) :
    ((withUnif (ctxtVfImpl aead k)) (.inr (.inl x))).run (L, b) =
      (@id (ProbComp
          ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))).Range (.inr (.inl x))))
        (aead.encrypt k x.1 x.2)) >>= fun c => pure (c, (L ++ [(x.1, @id C c)], b)) := by
  rw [ctxtVfImpl_enc, map_eq_bind_pure_comp]; rfl

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtVfImpl_vf (aead : Scheme ProbComp Msg Key AD C) (k : Key) (p : AD × C)
    (L : List (AD × C)) (b : Bool) :
    ((withUnif (ctxtVfImpl aead k)) (.inr (.inr p))).run (L, b) =
      pure ((aead.decrypt k p.1 p.2).isSome,
        (L, b || ((aead.decrypt k p.1 p.2).isSome && decide (p ∉ L)))) := by
  simp [withUnif, ctxtVfImpl]

/-- A pointwise bound by a finite sum lifts through a common first step. -/
private theorem probEvent_bind_le_sum {β γ δ : Type} {mx : ProbComp β} {f : β → ProbComp γ}
    {g : ℕ → β → ProbComp δ} {P : γ → Prop} {Q : δ → Prop} {n : ℕ}
    (h : ∀ x ∈ support mx, Pr[ P | f x] ≤ ∑ i ∈ Finset.range n, Pr[ Q | g i x]) :
    Pr[ P | mx >>= f] ≤ ∑ i ∈ Finset.range n, Pr[ Q | mx >>= g i] := by
  simp only [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[ P | f x]
      ≤ ∑' x, Pr[= x | mx] * ∑ i ∈ Finset.range n, Pr[ Q | g i x] := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact mul_le_mul' le_rfl (h x hx)
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = ∑' x, ∑ i ∈ Finset.range n, Pr[= x | mx] * Pr[ Q | g i x] := by
        simp only [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range n, ∑' x, Pr[= x | mx] * Pr[ Q | g i x] := by
        exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable

/-- The plain game's win event, read off a final state of `vfGuessGameImpl`. -/
private def vfWin (aead : Scheme ProbComp Msg Key AD C) (k : Key) (fallback : AD × C)
    (s : GuessState (AD × C) (AD × C) × List (AD × C)) : Bool :=
  (aead.decrypt k (s.1.guess.getD fallback).1 (s.1.guess.getD fallback).2).isSome &&
    decide (s.1.guess.getD fallback ∉ s.2)

omit [DecidableEq Msg] [SampleableType Key] in
/-- After a capture of a fresh valid pair, the plain game is won with probability 1: the
reduction's guess and the plain game's log no longer change. -/
private theorem vfGuessGame_capture (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C)
    (j : ℕ) (k : Key) {α : Type}
    (oa : OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))) α)
    (g : GuessState (AD × C) (AD × C)) (p : AD × C) (hg : g.guess = some p)
    (L : List (AD × C)) (hp : (aead.decrypt k p.1 p.2).isSome) (hpL : p ∉ L) :
    Pr[fun z => vfWin aead k fallback z.2 = true |
      (simulateQ (vfGuessGameImpl aead fallback j k) oa).run (g, L)] = 1 := by
  rw [probEvent_eq_one_iff]
  refine ⟨by simp, fun z hz => ?_⟩
  have hinv := simulateQ_run_preserves_inv_of_query (vfGuessGameImpl aead fallback j k)
    (fun s => s.1.guess = some p ∧ s.2 = L) (fun t s hs y hy => ?_) oa (g, L) ⟨hg, rfl⟩ z hz
  · obtain ⟨h1, h2⟩ := hinv
    simp [vfWin, h1, h2, hp, hpL]
  · obtain ⟨g', L'⟩ := s
    obtain ⟨hs1, hs2⟩ := hs
    rcases t with n | x | q
    · rw [vfGuessGameImpl_unif] at hy
      obtain ⟨u, rfl⟩ : y ∈ Set.range fun u => (u, g', L') := by simpa using hy
      exact ⟨hs1, hs2⟩
    · rw [vfGuessGameImpl_enc_some aead fallback j k x g' p hs1] at hy
      obtain rfl : y = (fallback.2, (g', L')) := hy
      exact ⟨hs1, hs2⟩
    · rw [vfGuessGameImpl_vf] at hy
      obtain rfl : y = (decide (q ∈ g'.log),
          (⟨g'.log, g'.seen + 1, g'.guess.or (if g'.seen = j then some q else none)⟩, L')) := hy
      exact ⟨by rw [show g'.guess = some p from hs1]; rfl, hs2⟩

omit [DecidableEq AD] [DecidableEq C] in
/-- For a perfectly correct scheme, decryption inverts encryption under every key and
associated data. -/
theorem decrypt_eq_of_mem_support_encrypt {aead : Scheme ProbComp Msg Key AD C}
    (hcorrect : PerfectlyCorrect aead) (k : Key) (ad : AD) (m : Msg) {c : C}
    (hc : c ∈ support (aead.encrypt k ad m)) :
    aead.decrypt k ad c = some m := by
  have h := hcorrect m ad
  rw [probOutput_eq_one_iff] at h
  have hmem : decide (aead.decrypt k ad c = some m) ∈ support (CorrectExp aead m ad) := by
    unfold CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨k, mem_support_uniformSample Key, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨c, hc, ?_⟩
    simp
  rw [h.2] at hmem
  simpa using hmem

/-- The core bound: from a log `L` of valid pairs, the verification game's flag has
probability at most the sum, over the next `n` verification-query indices, of the plain game's
win probability for the reduction that captures that index. -/
private theorem vfGuessGame_core (aead : Scheme ProbComp Msg Key AD C)
    (hcorrect : PerfectlyCorrect aead) (fallback : AD × C) (k : Key) {α : Type}
    (oa : OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))) α) :
    ∀ (n c : ℕ) (L : List (AD × C)), oa.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) n →
      (∀ p ∈ L, (aead.decrypt k p.1 p.2).isSome) →
      Pr[fun z => z.2.2 = true | (simulateQ (withUnif (ctxtVfImpl aead k)) oa).run (L, false)] ≤
        ∑ i ∈ Finset.range n, Pr[fun z => vfWin aead k fallback z.2 = true |
          (simulateQ (vfGuessGameImpl aead fallback (c + i) k) oa).run (⟨L, c, none⟩, L)] := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro n c L _ _
    simp
  | query_bind t mx ih =>
    intro n c L hb hL
    rw [isQueryBoundP_query_bind_iff] at hb
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    rcases t with u | x | p
    · rw [ctxtVfImpl_unif']
      simp only [vfGuessGameImpl_unif', bind_assoc, pure_bind]
      exact probEvent_bind_le_sum fun u _ => ih u n c L (by simpa using hb.2 u) hL
    · rw [ctxtVfImpl_enc']
      simp only [vfGuessGameImpl_enc_none', bind_assoc, pure_bind]
      refine probEvent_bind_le_sum fun cc hcc => ih cc n c _ (by simpa using hb.2 cc) ?_
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact hL q hq
      · obtain rfl : q = (x.1, cc) := List.mem_singleton.1 hq
        simp [decrypt_eq_of_mem_support_encrypt hcorrect k x.1 x.2 hcc]
    · rw [ctxtVfImpl_vf]
      simp only [vfGuessGameImpl_vf]
      have hn : 0 < n := by simpa using hb.1
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      by_cases hfresh : (aead.decrypt k p.1 p.2).isSome = true ∧ p ∉ L
      · refine le_trans ?_
          (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_range.2 (Nat.succ_pos n')))
        refine le_trans probEvent_le_one (le_of_eq ?_)
        exact (vfGuessGame_capture aead fallback (c + 0) k _ _ p (by simp) L
          hfresh.1 hfresh.2).symm
      · have hok : (aead.decrypt k p.1 p.2).isSome = decide (p ∈ L) := by
          by_cases hpL : p ∈ L
          · simp [hpL, hL p hpL]
          · simp only [hpL, decide_false]
            simpa [hpL] using hfresh
        have hflag : (false || ((aead.decrypt k p.1 p.2).isSome && decide (p ∉ L))) = false := by
          simpa [Bool.and_eq_true] using hfresh
        rw [hflag, hok, Finset.sum_range_succ']
        refine le_add_right ((ih (decide (p ∈ L)) n' (c + 1) L (by simpa using hb.2 _) hL).trans
          (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)))
        have h1 : c + 1 + i = c + (i + 1) := by omega
        have h2 : ¬ c = c + (i + 1) := by omega
        rw [h1, if_neg h2]
        rfl

omit [DecidableEq Msg] in
private theorem INT_CTXT_VF_Game_eq (aead : Scheme ProbComp Msg Key AD C)
    (B : INT_CTXT_VF_Adversary aead) :
    INT_CTXT_VF_Game aead B = ($ᵗ Key : ProbComp Key) >>= fun k =>
      (fun z => z.2.2) <$> (simulateQ (withUnif (ctxtVfImpl aead k)) B.run).run ([], false) := by
  unfold INT_CTXT_VF_Game
  refine bind_congr fun k => ?_
  rw [map_eq_bind_pure_comp]
  rfl

omit [DecidableEq Msg] in
private theorem INT_CTXT_Game_vfToCtxtAt_eq (aead : Scheme ProbComp Msg Key AD C)
    (fallback : AD × C) (j : ℕ) (B : INT_CTXT_VF_Adversary aead) :
    INT_CTXT_Game aead (vfToCtxtAt fallback j B) = ($ᵗ Key : ProbComp Key) >>= fun k =>
      (fun z => vfWin aead k fallback z.2) <$>
        (simulateQ (vfGuessGameImpl aead fallback j k) B.run).run (⟨[], 0, none⟩, []) := by
  unfold INT_CTXT_Game vfToCtxtAt
  refine bind_congr fun k => ?_
  rw [simulateQ_map, StateT.run_map, simulateQ_StateT_StateT_compose (vfGuessImpl fallback j)
    (withUnif (ctxtImpl aead k)) (vfGuessGameImpl aead fallback j k) (fun q s c => by
      simp [vfGuessGameImpl, StateT.mk]) B.run ⟨[], 0, none⟩ []]
  simp [vfWin, map_eq_bind_pure_comp]

omit [DecidableEq Msg] in
private theorem INT_CTXT_Game_eq (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_Adversary aead) :
    INT_CTXT_Game aead A = ($ᵗ Key : ProbComp Key) >>= fun k =>
      (fun r => (aead.decrypt k r.1.1 r.1.2).isSome && decide (r.1 ∉ r.2)) <$>
        (simulateQ (withUnif (ctxtImpl aead k)) A.run).run [] := by
  unfold INT_CTXT_Game
  refine bind_congr fun k => ?_
  rw [map_eq_bind_pure_comp]
  rfl

omit [DecidableEq Msg] [SampleableType Key] in
private theorem run_vfToCtxt_succ (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C)
    (v' : ℕ) (B : INT_CTXT_VF_Adversary aead) (k : Key) :
    (simulateQ (withUnif (ctxtImpl aead k)) (vfToCtxt fallback (v' + 1) B).run).run [] =
      (liftM (OracleSpec.query (spec := unifSpec) v') : ProbComp (Fin (v' + 1))) >>= fun i =>
        (simulateQ (withUnif (ctxtImpl aead k)) (vfToCtxtAt fallback i.val B).run).run [] := by
  simp [vfToCtxt, withUnif]

omit [DecidableEq Msg] in
/-- The plain game of `vfToCtxt fallback (v' + 1) B` averages the plain games of the
fixed-index reductions. -/
private theorem probOutput_INT_CTXT_Game_vfToCtxt_succ (aead : Scheme ProbComp Msg Key AD C)
    (fallback : AD × C) (v' : ℕ) (B : INT_CTXT_VF_Adversary aead) :
    Pr[= true | INT_CTXT_Game aead (vfToCtxt fallback (v' + 1) B)] =
      ∑ i ∈ Finset.range (v' + 1), (v' + 1 : ℝ≥0∞)⁻¹ *
        Pr[= true | INT_CTXT_Game aead (vfToCtxtAt fallback i B)] := by
  rw [INT_CTXT_Game_eq]
  simp only [run_vfToCtxt_succ, map_bind]
  rw [probOutput_bind_bind_swap, probOutput_bind_eq_tsum, tsum_fintype,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [probOutput_query, INT_CTXT_Game_eq]
  simp

private theorem probOutput_INT_CTXT_VF_Game_le_sum (aead : Scheme ProbComp Msg Key AD C)
    (hcorrect : PerfectlyCorrect aead) (fallback : AD × C) (B : INT_CTXT_VF_Adversary aead)
    (v : ℕ) (hv : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) v) :
    Pr[= true | INT_CTXT_VF_Game aead B] ≤
      ∑ i ∈ Finset.range v, Pr[= true | INT_CTXT_Game aead (vfToCtxtAt fallback i B)] := by
  simp only [INT_CTXT_VF_Game_eq, INT_CTXT_Game_vfToCtxtAt_eq, ← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_sum fun k _ => ?_
  simp only [probEvent_map, Function.comp_def]
  simpa using vfGuessGame_core aead hcorrect fallback k B.run v 0 [] hv (by simp)

omit [DecidableEq Msg] [SampleableType Key] in
/-- `vfToCtxt fallback v B` makes at most as many encryption queries as `B`. -/
theorem vfToCtxt_encBound {aead : Scheme ProbComp Msg Key AD C}
    (fallback : AD × C) (v : ℕ) (B : INT_CTXT_VF_Adversary aead) {e : ℕ}
    (he : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inl _)) e) :
    (vfToCtxt fallback v B).run.IsQueryBoundP (· matches Sum.inr _) e := by
  refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun i => ?_⟩
  simp only [vfToCtxtAt, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step he (fun t s => ?_) _
  rcases t with n | x | p
  · simpa [vfGuessImpl] using (isQueryBoundP_query_iff
      (spec := unifSpec + ((AD × Msg) →ₒ C)) (· matches Sum.inr _) (.inl n) 0).2 (by simp)
  · rcases hg : s.guess with _ | q
    · simpa [vfGuessImpl, hg] using (isQueryBoundP_query_iff
        (spec := unifSpec + ((AD × Msg) →ₒ C)) (· matches Sum.inr _) (.inr x) 1).2 (by simp)
    · simp [vfGuessImpl, hg]
  · simp [vfGuessImpl]

/-- The message `msg` of the first entry `(ad, msg, c)` of the log `L` with `(ad, c) = p`, or
`none`. The decryption reduction answers decryption queries with it. -/
def logLookup (L : List (AD × Msg × C)) (p : AD × C) : Option Msg :=
  match L.find? fun (ad, _, c) => decide ((ad, c) = p) with
  | some (_, msg, _) => some msg
  | none => none

/-- The handler of `decToCtxtAt fallback j`: as `vfGuessImpl`, with a log of encryption
queries and their answers, and decryption queries answered by `logLookup`. -/
def decGuessImpl (fallback : AD × C) (j : ℕ) :
    QueryImpl (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg)))
      (StateT (GuessState (AD × Msg × C) (AD × C)) (OracleComp (unifSpec + ((AD × Msg) →ₒ C))))
  | .inl n => liftM (OracleSpec.query (spec := unifSpec + ((AD × Msg) →ₒ C)) (.inl n))
  | .inr (.inl x) => do
      let s ← get
      match s.guess with
      | none =>
        let c : C ← liftM (OracleSpec.query (spec := unifSpec + ((AD × Msg) →ₒ C)) (.inr x))
        set { s with log := s.log ++ [(x.1, x.2, c)] }
        pure c
      | some _ => pure fallback.2
  | .inr (.inr p) => do
      let s ← get
      set { s with seen := s.seen + 1, guess := s.guess.or (if s.seen = j then some p else none) }
      pure (logLookup s.log p)

/-- The plain adversary that runs `B` with `decGuessImpl fallback j` and outputs the captured
pair, or `fallback` if `B` makes at most `j` decryption queries. -/
def decToCtxtAt {aead : Scheme ProbComp Msg Key AD C} (fallback : AD × C) (j : ℕ)
    (B : INT_CTXT_D_Adversary aead) : INT_CTXT_Adversary aead :=
  ⟨(fun r => r.2.guess.getD fallback) <$>
    (simulateQ (decGuessImpl fallback j) B.run).run ⟨[], 0, none⟩⟩

/-- The plain adversary that draws an index `i` uniformly from `[0, v - 1]` and runs
`decToCtxtAt fallback i B`. -/
def decToCtxt {aead : Scheme ProbComp Msg Key AD C} (fallback : AD × C) (v : ℕ)
    (B : INT_CTXT_D_Adversary aead) : INT_CTXT_Adversary aead :=
  ⟨do
    let i : Fin (v - 1 + 1) ←
      liftM (OracleSpec.query (spec := unifSpec + ((AD × Msg) →ₒ C)) (.inl (v - 1)))
    (decToCtxtAt fallback i.val B).run⟩

/-- One step of `decGuessImpl` run inside the plain game, reordered as in `vfGuessGameImpl`. -/
private def decGuessGameImpl (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C) (j : ℕ)
    (k : Key) : QueryImpl (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg)))
      (StateT (GuessState (AD × Msg × C) (AD × C) × List (AD × C)) ProbComp) := fun q =>
  StateT.mk fun sc => (fun r => (r.1.1, r.1.2, r.2)) <$>
    (simulateQ (withUnif (ctxtImpl aead k)) ((decGuessImpl fallback j q).run sc.1)).run sc.2

omit [DecidableEq Msg] [SampleableType Key] in
private theorem decGuessGameImpl_unif (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C)
    (j : ℕ) (k : Key) (n : ℕ) (g : GuessState (AD × Msg × C) (AD × C)) (L : List (AD × C)) :
    ((decGuessGameImpl aead fallback j k) (.inl n)).run (g, L) =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp
        ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))).Range (.inl n))) >>=
        fun u => pure (u, (g, L)) := by
  have h : ((decGuessGameImpl aead fallback j k) (.inl n)).run (g, L) =
      (fun u => (u, (g, L))) <$> (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) := by
    simp [decGuessGameImpl, decGuessImpl, withUnif]
  rw [h, map_eq_bind_pure_comp]; rfl

omit [DecidableEq Msg] [SampleableType Key] in
private theorem decGuessGameImpl_enc_none (aead : Scheme ProbComp Msg Key AD C)
    (fallback : AD × C) (j : ℕ) (k : Key) (x : AD × Msg) (g : GuessState (AD × Msg × C) (AD × C))
    (hg : g.guess = none) (L : List (AD × C)) :
    ((decGuessGameImpl aead fallback j k) (.inr (.inl x))).run (g, L) =
      (@id (ProbComp
          ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))).Range (.inr (.inl x))))
        (aead.encrypt k x.1 x.2)) >>= fun c =>
        pure (c, ({ g with log := g.log ++ [(x.1, x.2, @id C c)] }, L ++ [(x.1, @id C c)])) := by
  have h : ((decGuessGameImpl aead fallback j k) (.inr (.inl x))).run (g, L) =
      (fun c => (c, ({ g with log := g.log ++ [(x.1, x.2, c)] }, L ++ [(x.1, c)]))) <$>
        aead.encrypt k x.1 x.2 := by
    simp [decGuessGameImpl, decGuessImpl, withUnif, ctxtImpl, hg]
  rw [h, map_eq_bind_pure_comp]; rfl

omit [DecidableEq Msg] [SampleableType Key] in
private theorem decGuessGameImpl_enc_some (aead : Scheme ProbComp Msg Key AD C)
    (fallback : AD × C) (j : ℕ) (k : Key) (x : AD × Msg) (g : GuessState (AD × Msg × C) (AD × C))
    (p : AD × C) (hg : g.guess = some p) (L : List (AD × C)) :
    ((decGuessGameImpl aead fallback j k) (.inr (.inl x))).run (g, L) =
      pure (fallback.2, (g, L)) := by
  simp [decGuessGameImpl, decGuessImpl, hg]

omit [DecidableEq Msg] [SampleableType Key] in
private theorem decGuessGameImpl_dec (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C)
    (j : ℕ) (k : Key) (p : AD × C) (g : GuessState (AD × Msg × C) (AD × C))
    (L : List (AD × C)) :
    ((decGuessGameImpl aead fallback j k) (.inr (.inr p))).run (g, L) =
      pure (@id ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))).Range
          (.inr (.inr p))) (logLookup g.log p),
        (⟨g.log, g.seen + 1, g.guess.or (if g.seen = j then some p else none)⟩, L)) := by
  simp [decGuessGameImpl, decGuessImpl]

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtDecImpl_unif (aead : Scheme ProbComp Msg Key AD C) (k : Key) (n : ℕ)
    (s : List (AD × C) × Bool) :
    ((withUnif (ctxtDecImpl aead k)) (.inl n)).run s =
      (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp
        ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))).Range (.inl n))) >>=
        fun u => pure (u, s) := by
  have h : ((withUnif (ctxtDecImpl aead k)) (.inl n)).run s =
      (fun u => (u, s)) <$> (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) := by
    simp [withUnif]
  rw [h, map_eq_bind_pure_comp]; rfl

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtDecImpl_enc (aead : Scheme ProbComp Msg Key AD C) (k : Key) (x : AD × Msg)
    (L : List (AD × C)) (b : Bool) :
    ((withUnif (ctxtDecImpl aead k)) (.inr (.inl x))).run (L, b) =
      (@id (ProbComp
          ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))).Range (.inr (.inl x))))
        (aead.encrypt k x.1 x.2)) >>= fun c => pure (c, (L ++ [(x.1, @id C c)], b)) := by
  have h : ((withUnif (ctxtDecImpl aead k)) (.inr (.inl x))).run (L, b) =
      (fun c => (c, (L ++ [(x.1, c)], b))) <$> aead.encrypt k x.1 x.2 := by
    simp [withUnif, ctxtDecImpl]
  rw [h, map_eq_bind_pure_comp]; rfl

omit [DecidableEq Msg] [SampleableType Key] in
private theorem ctxtDecImpl_dec (aead : Scheme ProbComp Msg Key AD C) (k : Key) (p : AD × C)
    (L : List (AD × C)) (b : Bool) :
    ((withUnif (ctxtDecImpl aead k)) (.inr (.inr p))).run (L, b) =
      pure (@id ((unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))).Range
          (.inr (.inr p))) (aead.decrypt k p.1 p.2),
        (L, b || ((aead.decrypt k p.1 p.2).isSome && decide (p ∉ L)))) := by
  simp [withUnif, ctxtDecImpl]

omit [DecidableEq Msg] [SampleableType Key] in
/-- If every entry of `R` decrypts to its own message, `logLookup` answers like decryption on
a logged pair and on a pair that does not decrypt. -/
private theorem logLookup_eq (aead : Scheme ProbComp Msg Key AD C) (k : Key)
    (R : List (AD × Msg × C)) (hR : ∀ e ∈ R, aead.decrypt k e.1 e.2.2 = some e.2.1)
    (p : AD × C) (h : p ∈ R.map (fun e => (e.1, e.2.2)) ∨ aead.decrypt k p.1 p.2 = none) :
    logLookup R p = aead.decrypt k p.1 p.2 := by
  unfold logLookup
  split
  next ad m c hfind =>
    have he := List.mem_of_find?_eq_some hfind
    have hp : (ad, c) = p := by simpa using List.find?_some hfind
    subst hp
    exact (hR _ he).symm
  next hfind =>
    rcases h with h | h
    · obtain ⟨⟨ad, m, c⟩, he, rfl⟩ := List.mem_map.1 h
      exact absurd (by simp) (List.find?_eq_none.1 hfind _ he)
    · exact h.symm

/-- The plain game's win event, read off a final state of `decGuessGameImpl`. -/
private def decWin (aead : Scheme ProbComp Msg Key AD C) (k : Key) (fallback : AD × C)
    (s : GuessState (AD × Msg × C) (AD × C) × List (AD × C)) : Bool :=
  (aead.decrypt k (s.1.guess.getD fallback).1 (s.1.guess.getD fallback).2).isSome &&
    decide (s.1.guess.getD fallback ∉ s.2)

omit [DecidableEq Msg] [SampleableType Key] in
private theorem decGuessGame_capture (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C)
    (j : ℕ) (k : Key) {α : Type}
    (oa : OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))) α)
    (g : GuessState (AD × Msg × C) (AD × C)) (p : AD × C) (hg : g.guess = some p)
    (L : List (AD × C)) (hp : (aead.decrypt k p.1 p.2).isSome) (hpL : p ∉ L) :
    Pr[fun z => decWin aead k fallback z.2 = true |
      (simulateQ (decGuessGameImpl aead fallback j k) oa).run (g, L)] = 1 := by
  rw [probEvent_eq_one_iff]
  refine ⟨by simp, fun z hz => ?_⟩
  have hinv := simulateQ_run_preserves_inv_of_query (decGuessGameImpl aead fallback j k)
    (fun s => s.1.guess = some p ∧ s.2 = L) (fun t s hs y hy => ?_) oa (g, L) ⟨hg, rfl⟩ z hz
  · obtain ⟨h1, h2⟩ := hinv
    simp [decWin, h1, h2, hp, hpL]
  · obtain ⟨g', L'⟩ := s
    obtain ⟨hs1, hs2⟩ := hs
    rcases t with n | x | q
    · rw [decGuessGameImpl_unif] at hy
      obtain ⟨u, rfl⟩ : y ∈ Set.range fun u => (u, g', L') := by simpa using hy
      exact ⟨hs1, hs2⟩
    · rw [decGuessGameImpl_enc_some aead fallback j k x g' p hs1] at hy
      obtain rfl : y = (fallback.2, (g', L')) := hy
      exact ⟨hs1, hs2⟩
    · rw [decGuessGameImpl_dec] at hy
      obtain rfl : y = (logLookup g'.log q,
          (⟨g'.log, g'.seen + 1, g'.guess.or (if g'.seen = j then some q else none)⟩, L')) := hy
      exact ⟨by rw [show g'.guess = some p from hs1]; rfl, hs2⟩

/-- The core bound for the decryption game, as `vfGuessGame_core`, with a log `R` of
encryption queries whose entries decrypt to their own messages. -/
private theorem decGuessGame_core (aead : Scheme ProbComp Msg Key AD C)
    (hcorrect : PerfectlyCorrect aead) (fallback : AD × C) (k : Key) {α : Type}
    (oa : OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))) α) :
    ∀ (n c : ℕ) (R : List (AD × Msg × C)), oa.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) n →
      (∀ e ∈ R, aead.decrypt k e.1 e.2.2 = some e.2.1) →
      Pr[fun z => z.2.2 = true | (simulateQ (withUnif (ctxtDecImpl aead k)) oa).run
          (R.map (fun e => (e.1, e.2.2)), false)] ≤
        ∑ i ∈ Finset.range n, Pr[fun z => decWin aead k fallback z.2 = true |
          (simulateQ (decGuessGameImpl aead fallback (c + i) k) oa).run
            (⟨R, c, none⟩, R.map (fun e => (e.1, e.2.2)))] := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro n c R _ _
    simp
  | query_bind t mx ih =>
    intro n c R hb hR
    rw [isQueryBoundP_query_bind_iff] at hb
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    rcases t with u | x | p
    · rw [ctxtDecImpl_unif]
      simp only [decGuessGameImpl_unif, bind_assoc, pure_bind]
      exact probEvent_bind_le_sum fun u _ => ih u n c R (by simpa using hb.2 u) hR
    · rw [ctxtDecImpl_enc]
      simp only [decGuessGameImpl_enc_none, bind_assoc, pure_bind]
      refine probEvent_bind_le_sum fun cc hcc => ?_
      have hR' : ∀ e ∈ R ++ [(x.1, x.2, @id C cc)], aead.decrypt k e.1 e.2.2 = some e.2.1 := by
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact hR e he
        · obtain rfl := List.mem_singleton.1 he
          exact decrypt_eq_of_mem_support_encrypt hcorrect k x.1 x.2 hcc
      simpa using ih cc n c (R ++ [(x.1, x.2, @id C cc)]) (by simpa using hb.2 cc) hR'
    · rw [ctxtDecImpl_dec]
      simp only [decGuessGameImpl_dec, pure_bind]
      have hn : 0 < n := by simpa using hb.1
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      by_cases hfresh : (aead.decrypt k p.1 p.2).isSome = true ∧
          p ∉ R.map (fun e => (e.1, e.2.2))
      · refine le_trans ?_
          (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_range.2 (Nat.succ_pos n')))
        refine le_trans probEvent_le_one (le_of_eq ?_)
        exact (decGuessGame_capture aead fallback (c + 0) k _ _ p (by simp) _
          hfresh.1 hfresh.2).symm
      · have hans : aead.decrypt k p.1 p.2 = logLookup R p := by
          refine (logLookup_eq aead k R hR p ?_).symm
          by_cases hpL : p ∈ R.map (fun e => (e.1, e.2.2))
          · exact Or.inl hpL
          · right
            simpa [hpL] using hfresh
        have hflag : (false || ((aead.decrypt k p.1 p.2).isSome &&
            decide (p ∉ R.map (fun e => (e.1, e.2.2))))) = false := by
          simpa [Bool.and_eq_true] using hfresh
        rw [hflag, hans, Finset.sum_range_succ']
        refine le_add_right ((ih (logLookup R p) n' (c + 1) R (by simpa using hb.2 _) hR).trans
          (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)))
        have h1 : c + 1 + i = c + (i + 1) := by omega
        have h2 : ¬ c = c + (i + 1) := by omega
        rw [h1, if_neg h2]
        rfl

omit [DecidableEq Msg] in
private theorem INT_CTXT_D_Game_eq (aead : Scheme ProbComp Msg Key AD C)
    (B : INT_CTXT_D_Adversary aead) :
    INT_CTXT_D_Game aead B = ($ᵗ Key : ProbComp Key) >>= fun k =>
      (fun z => z.2.2) <$> (simulateQ (withUnif (ctxtDecImpl aead k)) B.run).run ([], false) := by
  unfold INT_CTXT_D_Game
  refine bind_congr fun k => ?_
  rw [map_eq_bind_pure_comp]
  rfl

omit [DecidableEq Msg] in
private theorem INT_CTXT_Game_decToCtxtAt_eq (aead : Scheme ProbComp Msg Key AD C)
    (fallback : AD × C) (j : ℕ) (B : INT_CTXT_D_Adversary aead) :
    INT_CTXT_Game aead (decToCtxtAt fallback j B) = ($ᵗ Key : ProbComp Key) >>= fun k =>
      (fun z => decWin aead k fallback z.2) <$>
        (simulateQ (decGuessGameImpl aead fallback j k) B.run).run (⟨[], 0, none⟩, []) := by
  unfold INT_CTXT_Game decToCtxtAt
  refine bind_congr fun k => ?_
  rw [simulateQ_map, StateT.run_map, simulateQ_StateT_StateT_compose (decGuessImpl fallback j)
    (withUnif (ctxtImpl aead k)) (decGuessGameImpl aead fallback j k) (fun q s c => by
      simp [decGuessGameImpl, StateT.mk]) B.run ⟨[], 0, none⟩ []]
  simp [decWin, map_eq_bind_pure_comp]

omit [DecidableEq Msg] [SampleableType Key] in
private theorem run_decToCtxt_succ (aead : Scheme ProbComp Msg Key AD C) (fallback : AD × C)
    (v' : ℕ) (B : INT_CTXT_D_Adversary aead) (k : Key) :
    (simulateQ (withUnif (ctxtImpl aead k)) (decToCtxt fallback (v' + 1) B).run).run [] =
      (liftM (OracleSpec.query (spec := unifSpec) v') : ProbComp (Fin (v' + 1))) >>= fun i =>
        (simulateQ (withUnif (ctxtImpl aead k)) (decToCtxtAt fallback i.val B).run).run [] := by
  simp [decToCtxt, withUnif]

omit [DecidableEq Msg] in
/-- The plain game of `decToCtxt fallback (v' + 1) B` averages the plain games of the
fixed-index reductions. -/
private theorem probOutput_INT_CTXT_Game_decToCtxt_succ (aead : Scheme ProbComp Msg Key AD C)
    (fallback : AD × C) (v' : ℕ) (B : INT_CTXT_D_Adversary aead) :
    Pr[= true | INT_CTXT_Game aead (decToCtxt fallback (v' + 1) B)] =
      ∑ i ∈ Finset.range (v' + 1), (v' + 1 : ℝ≥0∞)⁻¹ *
        Pr[= true | INT_CTXT_Game aead (decToCtxtAt fallback i B)] := by
  rw [INT_CTXT_Game_eq]
  simp only [run_decToCtxt_succ, map_bind]
  rw [probOutput_bind_bind_swap, probOutput_bind_eq_tsum, tsum_fintype,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [probOutput_query, INT_CTXT_Game_eq]
  simp

private theorem probOutput_INT_CTXT_D_Game_le_sum (aead : Scheme ProbComp Msg Key AD C)
    (hcorrect : PerfectlyCorrect aead) (fallback : AD × C) (B : INT_CTXT_D_Adversary aead)
    (v : ℕ) (hv : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) v) :
    Pr[= true | INT_CTXT_D_Game aead B] ≤
      ∑ i ∈ Finset.range v, Pr[= true | INT_CTXT_Game aead (decToCtxtAt fallback i B)] := by
  simp only [INT_CTXT_D_Game_eq, INT_CTXT_Game_decToCtxtAt_eq, ← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_sum fun k _ => ?_
  simp only [probEvent_map, Function.comp_def]
  simpa using decGuessGame_core aead hcorrect fallback k B.run v 0 [] hv (by simp)

omit [DecidableEq Msg] [SampleableType Key] in
/-- `decToCtxt fallback v B` makes at most as many encryption queries as `B`. -/
theorem decToCtxt_encBound {aead : Scheme ProbComp Msg Key AD C}
    (fallback : AD × C) (v : ℕ) (B : INT_CTXT_D_Adversary aead) {e : ℕ}
    (he : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inl _)) e) :
    (decToCtxt fallback v B).run.IsQueryBoundP (· matches Sum.inr _) e := by
  refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp, fun i => ?_⟩
  simp only [decToCtxtAt, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step he (fun t s => ?_) _
  rcases t with n | x | p
  · simpa [decGuessImpl] using (isQueryBoundP_query_iff
      (spec := unifSpec + ((AD × Msg) →ₒ C)) (· matches Sum.inr _) (.inl n) 0).2 (by simp)
  · rcases hg : s.guess with _ | q
    · simpa [decGuessImpl, hg] using (isQueryBoundP_query_iff
        (spec := unifSpec + ((AD × Msg) →ₒ C)) (· matches Sum.inr _) (.inr x) 1).2 (by simp)
    · simp [decGuessImpl, hg]
  · simp [decGuessImpl]

/-! ## The four lemmas -/

omit [DecidableEq Msg] in
/-- Plain INT-CTXT is no harder than the verification-oracle variant: `ctxtToVf A` runs `A` and
submits its forgery to the verification oracle, and the two advantages are equal
(`INT_CTXT_VF_Advantage_ctxtToVf`). No PQXDH theorem uses this lemma. -/
theorem INT_CTXT_Advantage_le_INT_CTXT_VF_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (A : INT_CTXT_Adversary aead) :
    INT_CTXT_Advantage aead A ≤ INT_CTXT_VF_Advantage aead (ctxtToVf A) :=
  (INT_CTXT_VF_Advantage_ctxtToVf aead A).ge

/-- If `aead` is perfectly correct and `B` makes at most `v` verification queries, then for
every `fallback : AD × C`,
`INT_CTXT_VF_Advantage aead B ≤ v * INT_CTXT_Advantage aead (vfToCtxt fallback v B)`.

The reduction `vfToCtxt fallback v B` guesses which of `B`'s verification queries is the first
fresh valid one and outputs it. `hcorrect` lets it answer the earlier verification queries from
its log, since logged pairs decrypt. It outputs `fallback` when it captures nothing, and answers
encryption queries after the capture with `fallback.2`. The lemma has no instance when
`AD × C` is empty. No PQXDH theorem uses this lemma. -/
theorem INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (hcorrect : PerfectlyCorrect aead)
    (fallback : AD × C) (B : INT_CTXT_VF_Adversary aead) (v : ℕ)
    (hv : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) v) :
    INT_CTXT_VF_Advantage aead B ≤ (v : ℝ) * INT_CTXT_Advantage aead (vfToCtxt fallback v B) := by
  have key := probOutput_INT_CTXT_VF_Game_le_sum aead hcorrect fallback B v hv
  unfold INT_CTXT_VF_Advantage INT_CTXT_Advantage
  cases v with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, nonpos_iff_eq_zero] at key
    simp [key]
  | succ v' =>
    rw [probOutput_INT_CTXT_Game_vfToCtxt_succ, ← Finset.mul_sum] at *
    have hne : (v' + 1 : ℝ≥0∞) ≠ 0 := by simp
    have hsum : ∑ i ∈ Finset.range (v' + 1),
        Pr[= true | INT_CTXT_Game aead (vfToCtxtAt fallback i B)] =
        (v' + 1 : ℝ≥0∞) * ((v' + 1 : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (v' + 1),
          Pr[= true | INT_CTXT_Game aead (vfToCtxtAt fallback i B)]) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hne (by simp), one_mul]
    calc (Pr[= true | INT_CTXT_VF_Game aead B]).toReal
        ≤ ((v' + 1 : ℝ≥0∞) * ((v' + 1 : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (v' + 1),
          Pr[= true | INT_CTXT_Game aead (vfToCtxtAt fallback i B)])).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp)
            (ENNReal.sum_ne_top.2 fun _ _ => probOutput_ne_top))) (key.trans hsum.le)
      _ = _ := by rw [ENNReal.toReal_mul]; push_cast; rfl

omit [DecidableEq Msg] in
/-- Plain INT-CTXT is no harder than the decryption-oracle variant: `ctxtToDec A` runs `A` and
submits its forgery to the decryption oracle, and the two advantages are equal
(`INT_CTXT_D_Advantage_ctxtToDec`). No PQXDH theorem uses this lemma. The PQXDH security
theorems assume a bound on `INT_CTXT_D_Advantage` directly. -/
theorem INT_CTXT_Advantage_le_INT_CTXT_D_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (A : INT_CTXT_Adversary aead) :
    INT_CTXT_Advantage aead A ≤ INT_CTXT_D_Advantage aead (ctxtToDec A) :=
  (INT_CTXT_D_Advantage_ctxtToDec aead A).ge

/-- If `aead` is perfectly correct and `B` makes at most `v` decryption queries, then for every
`fallback : AD × C`,
`INT_CTXT_D_Advantage aead B ≤ v * INT_CTXT_Advantage aead (decToCtxt fallback v B)`.

The reduction `decToCtxt fallback v B` works as `vfToCtxt`: it guesses which of `B`'s
decryption queries is the first fresh valid one, and answers the earlier ones with `logLookup`,
which `hcorrect` makes agree with decryption on logged pairs. `fallback` plays the same role as
in `INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage`, so the lemma has no instance when
`AD × C` is empty. No PQXDH theorem uses this lemma. The PQXDH security theorems assume a bound
on `INT_CTXT_D_Advantage` directly. -/
theorem INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (hcorrect : PerfectlyCorrect aead)
    (fallback : AD × C) (B : INT_CTXT_D_Adversary aead) (v : ℕ)
    (hv : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) v) :
    INT_CTXT_D_Advantage aead B ≤ (v : ℝ) * INT_CTXT_Advantage aead (decToCtxt fallback v B) := by
  have key := probOutput_INT_CTXT_D_Game_le_sum aead hcorrect fallback B v hv
  unfold INT_CTXT_D_Advantage INT_CTXT_Advantage
  cases v with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, nonpos_iff_eq_zero] at key
    simp [key]
  | succ v' =>
    rw [probOutput_INT_CTXT_Game_decToCtxt_succ, ← Finset.mul_sum] at *
    have hne : (v' + 1 : ℝ≥0∞) ≠ 0 := by simp
    have hsum : ∑ i ∈ Finset.range (v' + 1),
        Pr[= true | INT_CTXT_Game aead (decToCtxtAt fallback i B)] =
        (v' + 1 : ℝ≥0∞) * ((v' + 1 : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (v' + 1),
          Pr[= true | INT_CTXT_Game aead (decToCtxtAt fallback i B)]) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hne (by simp), one_mul]
    calc (Pr[= true | INT_CTXT_D_Game aead B]).toReal
        ≤ ((v' + 1 : ℝ≥0∞) * ((v' + 1 : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (v' + 1),
          Pr[= true | INT_CTXT_Game aead (decToCtxtAt fallback i B)])).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp)
            (ENNReal.sum_ne_top.2 fun _ _ => probOutput_ne_top))) (key.trans hsum.le)
      _ = _ := by rw [ENNReal.toReal_mul]; push_cast; rfl

end AEAD
