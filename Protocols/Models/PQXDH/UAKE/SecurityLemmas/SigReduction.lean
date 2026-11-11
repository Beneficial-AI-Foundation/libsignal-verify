/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.OracleInvariants
import Protocols.ToVCVio.CryptoFoundations.JointSignatureAlg

/-!
# The reduction behind hop 3

Bob's identity secret `x` has three uses in the model: the signature of the signed pre-key in
`setup`, the signature of the KEM key in `publish`, and the Diffie-Hellman value
`DH p.ikB.2 msg.ekA` in `accept`. The reduction in this file runs the challenge phase of the UAKE
game against a copy of the scheme that never reads `x`. It answers the two signatures with
queries to the signing oracle and the Diffie-Hellman value with a query to the agreement oracle
of the joint unforgeability game (`SignatureAlg.jointUnforgeableExp`), and it samples everything
else itself. It outputs the signed key of the accepted bundle that the challenger never signed.

The reduction makes one signing query for `setup`, one signing query for each `openT` query of
the UAKE adversary, and one agreement query for each `stepT` query that reaches the computation
of `DH2` in `accept`. `OpensAtMost` bounds the openings only, and a rejected `stepT` query leaves
the session open for another try. So the number of agreement queries is not bounded by the number
of sessions. The file proves no resource bound for the reduction (#41).

The definitions and proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.Models.PQXDH

namespace SigReduction

noncomputable section

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- The oracles of the reduction: uniform sampling, signing, and agreement on the identity key. -/
abbrev Spec (G PQPK S : Type) :=
  SignatureAlg.JointSpec (SignatureInput G PQPK) S G G

/-- A query to the signing oracle. -/
def signQ (m : SignatureInput G PQPK) : OracleComp (Spec G PQPK S) S :=
  liftM (OracleSpec.query (spec := Spec G PQPK S) (.inr (.inl m)))

/-- A query to the agreement oracle. -/
def agreeQ (Y : G) : OracleComp (Spec G PQPK S) G :=
  liftM (OracleSpec.query (spec := Spec G PQPK S) (.inr (.inr Y)))

/-- A uniform-sampling computation, lifted to the oracles of the reduction. -/
def up {α : Type} (c : ProbComp α) : OracleComp (Spec G PQPK S) α :=
  liftM c

/-- `publish` with the KEM-key signature taken from the signing oracle. -/
def publishSim (p : RecipientParameters F G PQPK PQSK S) :
    OracleComp (Spec G PQPK S) (PreKeyBundle G PQPK S IdC IdK) := do
  let pqpkSigB ← signQ (EncodeKEM p.pqpkB.1)
  return { ikB := p.ikB.1
           spkB := (p.spkB.1, P.idEC p.spkB.1)
           spkSigB := p.spkSigB
           pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
           pqpkSigB := pqpkSigB
           opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) }

/-- `accept` with the value `DH2` taken from the agreement oracle. -/
def acceptSim (p : RecipientParameters F G PQPK PQSK S)
    (msg : InitialMessage G CT C IdC IdK) :
    OracleComp (Spec G PQPK S) (Option (SessionContext G PQPK Msg K)) := do
  if msg.idSPK ≠ P.idEC p.spkB.1 ∨ msg.idPQPK ≠ P.idKEM p.pqpkB.1 ∨
      msg.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.1) then return none
  let some SS ← up (P.pqkem.decaps p.pqpkB.2 msg.ct) | return none
  let DH1 := DH p.spkB.2 msg.ikA
  let DH2 ← agreeQ msg.ekA
  let DH3 := DH p.spkB.2 msg.ekA
  let DH4 := p.opkB.map fun opk => DH opk.2 msg.ekA
  let (SK, KA, KB) := P.kdf (DH1, DH2, DH3, DH4, SS)
  let AD := (msg.ikA, p.ikB.1, p.pqpkB.1)
  match P.aead.decrypt KA AD msg.ctxt with
  | some m => return some { sk := SK, kb := KB, ad := AD, msg := m }
  | none => return none

/-- Bob's party of the reduction: `recipient` with `publishSim` and `acceptSim`. Its state type is
that of `recipient`, and it never reads the secret half of the identity key. -/
def recipientSim :
    Party (OracleComp (Spec G PQPK S)) (RecipientIdentity F G S)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G PQPK PQSK S ⊕ K
  init := fun idn => do
    let opkB ← up (genOPK P.gen hasOPK)
    let pqpkB ← up P.pqkem.keygen
    let p : RecipientParameters F G PQPK PQSK S :=
      { ikB := idn.ikB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publishSim P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← acceptSim P p im with
        | some ctx => do
            let conf ← up (P.aead.encrypt ctx.kb ctx.ad ctx.msg)
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

/-- Alice's party of the reduction: `initiator` with its computations lifted to the oracles of the
reduction. -/
def initiatorSim :
    Party (OracleComp (Spec G PQPK S)) (InitiatorParameters F G Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← up (initiate P p b) with
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

/-- The long-term state of the reduction. Bob's identity public key `pk` comes from the signing
challenge, and his secret half is a placeholder that no procedure of the reduction reads. -/
def setupSim [Inhabited F] (pk : G) :
    OracleComp (Spec G PQPK S) (InitiatorParameters F G Msg × RecipientIdentity F G S) := do
  let ikA ← up (dhKeygen (F := F) P.gen)
  let spkB ← up (dhKeygen (F := F) P.gen)
  let spkSigB ← signQ (EncodeEC spkB.1)
  return ({ ikA := ikA, ikB := pk, msg := msg },
    { ikB := (pk, default), spkB := spkB, spkSigB := spkSigB })

/-- The UAKE scheme of the reduction, for the identity public key `pk`. -/
def uakeInitiatorSim [Inhabited F] (pk : G) :
    UAKE.Scheme (OracleComp (Spec G PQPK S)) K (InitiatorParameters F G Msg)
      (RecipientIdentity F G S) (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setupSim P msg pk
  U := initiatorSim P
  T := recipientSim P hasOPK

/-- The pair that the reduction outputs: the signed key of the accepted bundle that the
challenger never signed, with its signature. Without an accepted bundle, it is the signed
pre-key of `setup` with its signature. The reduction had that key signed, so it is no forgery. -/
def forgery (tk : RecipientIdentity F G S) (tr : Transcript (Message G PQPK CT S C IdC IdK)) :
    SignatureInput G PQPK × S :=
  match transcriptBundle tr with
  | some b =>
      if b.spkB.1 = tk.spkB.1 then (EncodeKEM b.pqpkB.1, b.pqpkSigB)
      else (EncodeEC b.spkB.1, b.spkSigB)
  | none => (EncodeEC tk.spkB.1, tk.spkSigB)

/-- The reduction. Given Bob's identity public key, it runs the challenge phase of the UAKE game
against `uakeInitiatorSim` and outputs `forgery`. -/
def sigAdversary [Inhabited F] (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    P.sig.JointAdversary (DH : F → G → G) where
  main pk := do
    let (uk, tk) ← setupSim (S := S) (PQPK := PQPK) (Msg := Msg) P msg pk
    let (cr, _) ← challengeSession (ProbCompLift.ofMonadLift (OracleComp (Spec G PQPK S)))
      (proto := uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) P msg hasOPK pk)
      ⟨A.State, A.challenge, A.post⟩ uk tk
    pure (forgery tk cr.challengeTr)

/-! ## The state map and the invariant of the real challenge phase

The real challenge phase and the reduction run on environments that differ in one place: the
sessions of Bob hold the secret half of the identity key in the real run and a placeholder in
the reduction. `scrubEnv` maps the first to the second. The reduction's signing log is a function
of the real environment: `signedLog` lists the KEM keys of the bundles that the sessions of Bob
published, newest first, and then the signed pre-key. -/

/-- The oracle of the real challenge stage, for Bob's identity `tk`. -/
abbrev realImpl (tk : RecipientIdentity F G S) :=
  oracleImpl ProbCompRuntime.probComp.toProbCompLift (uakeInitiator P msg hasOPK) tk

/-- Bob's identity with the secret half of the identity key replaced by a placeholder. -/
def scrubId [Inhabited F] (tk : RecipientIdentity F G S) : RecipientIdentity F G S :=
  { tk with ikB := (tk.ikB.1, default) }

/-- The oracle of the challenge stage of the reduction, for Bob's identity `tk`. -/
abbrev simImpl [Inhabited F] (pk : G) (tk : RecipientIdentity F G S) :=
  oracleImpl (ProbCompLift.ofMonadLift (OracleComp (Spec G PQPK S)))
    (uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) P msg hasOPK pk) tk

/-- The oracles of the joint game for Bob's identity key pair `(pk, x)`. -/
abbrev jointOr [Inhabited F] (pk : G) (x : F) :=
  SignatureAlg.jointImpl P.sig (DH : F → G → G) pk x

/-- A session state of Bob with the secret half of the identity key replaced by a placeholder. -/
def scrubState [Inhabited F] :
    RecipientParameters F G PQPK PQSK S ⊕ K → RecipientParameters F G PQPK PQSK S ⊕ K
  | .inl p => .inl { p with ikB := (p.ikB.1, default) }
  | .inr k => .inr k

/-- The environment of the real run, as the reduction sees it. -/
def scrubEnv [Inhabited F] (pk : G) (env : Env (uakeInitiator P msg hasOPK)) :
    Env (uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) P msg hasOPK pk) :=
  ⟨env.clock, env.challenge, env.challengeDone,
    env.tSessions.map fun t => ⟨scrubState t.state, t.transcript, t.key, t.revealed⟩⟩

/-- The messages that the reduction has had signed, newest first, as a function of the real
environment: the KEM keys of the bundles that the sessions of Bob published, and the signed
pre-key of `setup`. -/
def signedLog (tk : RecipientIdentity F G S) (env : Env (uakeInitiator P msg hasOPK)) :
    List (SignatureInput G PQPK) :=
  (((env.tSessions.map (·.transcript)).filterMap transcriptBundle).map
    fun b => (EncodeKEM b.pqpkB.1 : SignatureInput G PQPK)).reverse ++ [EncodeEC tk.spkB.1]

/-- Both signatures of the bundle `b` verify under the identity public key `pk`, as possible
outcomes of the verification. -/
def Verified (pk : G) (b : PreKeyBundle G PQPK S IdC IdK) : Prop :=
  true ∈ support (P.sig.verify pk (EncodeEC b.spkB.1) b.spkSigB) ∧
    true ∈ support (P.sig.verify pk (EncodeKEM b.pqpkB.1) b.pqpkSigB)

/-- The invariant of the real challenge phase, for Bob's identity key pair `(pk, x)` and Alice's
initial state `uk`:
* Alice pins Bob's public key;
* every session of Bob starts with the bundle he published, and holds the identity key pair
  `(pk, x)` as long as it has not accepted;
* the challenge session either has not accepted a bundle, and then has an empty transcript and
  its initial state, or its transcript starts with a bundle whose signatures verified. -/
structure SimInv [Inhabited F] (pk : G) (x : F) (uk : InitiatorParameters F G Msg)
    (env : Env (uakeInitiator P msg hasOPK)) : Prop where
  pinned : uk.ikB = pk
  sessions : ∀ t ∈ env.tSessions,
    (∃ b c es, t.transcript.entries = (Message.bundle b, c) :: es) ∧
      ∀ p : RecipientParameters F G PQPK PQSK S,
        t.state = (Sum.inl p : RecipientParameters F G PQPK PQSK S ⊕ K) → p.ikB = (pk, x)
  challenge :
    (env.challenge.state =
          (Sum.inl uk : InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K ⊕ K) ∧
        env.challenge.transcript.entries = []) ∨
      ∃ b c es, env.challenge.transcript.entries = (Message.bundle b, c) :: es ∧
        Verified P pk b

/-! ## The parties of the reduction under the joint oracles

Each lemma says that a computation of the reduction, run against the joint oracles for the key
pair `(pk, x)`, equals the corresponding real computation, with the signing log extended by the
messages that the reduction had signed. -/

omit [AddCommGroup G] [DecidableEq G] [DecidableEq PQPK] in
lemma run_unif {α : Type} (c : ProbComp α) (log : List (SignatureInput G PQPK)) :
    (simulateQ (fun t : unifSpec.Domain =>
      (liftM ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) t) :
        StateT (List (SignatureInput G PQPK)) ProbComp _)) c).run log =
      (fun a => (a, log)) <$> c := by
  induction c using OracleComp.inductionOn generalizing log with
  | pure a => simp
  | query_bind t k ih =>
    rw [OracleComp.run_simulateQ_query_bind]
    simp only [StateT.run_monadLift, bind_assoc, pure_bind, map_bind]
    exact bind_congr fun a => ih a log

omit [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K] [DecidableEq G]
 [DecidableEq PQPK] in
lemma run_up [Inhabited F] {α : Type} (pk : G) (x : F) (c : ProbComp α)
    (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x) (up (G := G) (PQPK := PQPK) (S := S) c)).run log =
      (fun a => (a, log)) <$> c := by
  unfold up
  simp only [jointOr, SignatureAlg.jointImpl]
  rw [QueryImpl.simulateQ_add_liftM_left]
  exact run_unif c log

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
 [SampleableType K] in
lemma run_signQ [Inhabited F] (pk : G) (x : F) (m : SignatureInput G PQPK)
    (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x) (signQ (S := S) m)).run log =
      (fun σ => (σ, m :: log)) <$> P.sign pk x m := by
  simp [jointOr, signQ, SignatureAlg.jointImpl]

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
 [SampleableType K] in
lemma run_agreeQ [Inhabited F] (pk : G) (x : F) (Y : G)
    (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x) (agreeQ (S := S) (PQPK := PQPK) Y)).run log =
      pure (DH x Y, log) := by
  simp [jointOr, agreeQ, SignatureAlg.jointImpl]

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
 [SampleableType K] in
lemma run_publishSim [Inhabited F] (pk : G) (x : F)
    (p : RecipientParameters F G PQPK PQSK S) (hp : p.ikB = (pk, x))
    (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x)
      (publishSim (IdC := IdC) (IdK := IdK) (C := C) (K := K) P
        { p with ikB := (p.ikB.1, default) })).run log =
      (fun b => (b, (EncodeKEM b.pqpkB.1 : SignatureInput G PQPK) :: log)) <$>
        (publish (IdC := IdC) (IdK := IdK) (C := C) (K := K) P p) := by
  simp [publishSim, publish, run_signQ, hp]

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [SampleableType K] in
lemma run_acceptSim [Inhabited F] (pk : G) (x : F)
    (p : RecipientParameters F G PQPK PQSK S) (hp : p.ikB = (pk, x))
    (im : InitialMessage G CT C IdC IdK)
    (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x)
      (acceptSim (Msg := Msg) (K := K) P { p with ikB := (p.ikB.1, default) } im)).run log =
      (fun r => (r, log)) <$> accept P p im := by
  unfold acceptSim accept
  by_cases hid : im.idSPK ≠ P.idEC p.spkB.1 ∨ im.idPQPK ≠ P.idKEM p.pqpkB.1 ∨
      im.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.1)
  · simp [hid]
  · simp only [hid, ite_false]
    simp only [simulateQ_bind, StateT.run_bind, run_up, map_bind, bind_map_left]
    refine bind_congr fun r => ?_
    rcases r with _ | SS
    · simp
    · simp only [hp, simulateQ_bind, StateT.run_bind, run_agreeQ, pure_bind]
      rcases hd : P.aead.decrypt (P.kdf (DH p.spkB.2 im.ikA, DH x im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, SS)).2.1 (im.ikA, pk, p.pqpkB.1) im.ctxt
        with _ | m <;> simp [hd]

/-- The initial result of a session of Bob, with the secret placeholder. -/
def scrubInit [Inhabited F] :
    Party.InitResult (RecipientParameters F G PQPK PQSK S ⊕ K) (Message G PQPK CT S C IdC IdK) →
      Party.InitResult (RecipientParameters F G PQPK PQSK S ⊕ K) (Message G PQPK CT S C IdC IdK)
  | .speakFirst st w => .speakFirst (scrubState st) w
  | .waitForMsg st => .waitForMsg (scrubState st)

/-- The message that an initial result signs: the KEM key of the bundle that it opens with. -/
def initLog :
    Party.InitResult (RecipientParameters F G PQPK PQSK S ⊕ K) (Message G PQPK CT S C IdC IdK) →
      List (SignatureInput G PQPK)
  | .speakFirst _ (.bundle b) => [EncodeKEM b.pqpkB.1]
  | _ => []

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [SampleableType K] in
lemma run_recipientSim_init [Inhabited F] (pk : G) (x : F) (tk : RecipientIdentity F G S)
    (htk : tk.ikB = (pk, x)) (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x) ((recipientSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK)
      (K := K) P hasOPK).init (scrubId tk))).run log =
      (fun r => (scrubInit r, initLog r ++ log)) <$> (recipient P hasOPK).init tk := by
  simp only [recipientSim, recipient, simulateQ_bind, StateT.run_bind, run_up, map_bind,
    bind_map_left]
  refine bind_congr fun opkB => bind_congr fun pqpkB => ?_
  have hpub := run_publishSim (IdC := IdC) (IdK := IdK) (C := C) (K := K) P pk x
    { ikB := tk.ikB, spkB := tk.spkB, spkSigB := tk.spkSigB, opkB := opkB, pqpkB := pqpkB }
    htk log
  simp only [scrubId] at hpub ⊢
  rw [hpub]
  simp [scrubInit, initLog, scrubState]

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [SampleableType K] in
lemma run_recipientSim_step [Inhabited F] (pk : G) (x : F)
    (st : RecipientParameters F G PQPK PQSK S ⊕ K)
    (hst : ∀ p, st = Sum.inl p → p.ikB = (pk, x))
    (w : Message G PQPK CT S C IdC IdK) (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x) ((recipientSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK)
      (K := K) P hasOPK).step (scrubState st) w)).run log =
      (fun r => (r, log)) <$> (recipient P hasOPK).step st w := by
  rcases st with p | k
  · rcases w with b | im | conf
    · simp [recipientSim, recipient, scrubState]
    · have hp := hst p rfl
      simp only [recipientSim, recipient, scrubState]
      have hacc := run_acceptSim (Msg := Msg) (K := K) P pk x p hp im log
      simp only [simulateQ_bind, StateT.run_bind, hacc, map_bind, bind_map_left]
      refine bind_congr fun r => ?_
      rcases r with _ | ctx
      · simp
      · simp [run_up]
    · simp [recipientSim, recipient, scrubState]
  · simp [recipientSim, recipient, scrubState]

omit [DecidableEq PQPK] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K] in
lemma run_initiatorSim_step [Inhabited F] (pk : G) (x : F)
    (st : InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (w : Message G PQPK CT S C IdC IdK) (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x) ((initiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK)
      (K := K) P).step st w)).run log =
      (fun r => (r, log)) <$> (initiator P).step st w := by
  rcases st with p | ctx | k
  · rcases w with b | im | conf
    · simp only [initiatorSim, initiator, simulateQ_bind, StateT.run_bind, run_up, map_bind,
        bind_map_left]
      refine bind_congr fun r => ?_
      rcases r with _ | ⟨im, ctx⟩ <;> simp
    · simp [initiatorSim, initiator]
    · simp [initiatorSim, initiator]
  · rcases w with b | im | conf
    · simp [initiatorSim, initiator]
    · simp [initiatorSim, initiator]
    · simp only [initiatorSim, initiator]
      rcases hc : confirm P ctx conf with _ | SK <;> simp
  · simp [initiatorSim, initiator]

omit [DecidableEq PQPK] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K] in
lemma run_initiatorSim_init [Inhabited F] (pk : G) (x : F) (uk : InitiatorParameters F G Msg)
    (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x) ((initiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK)
      (K := K) P).init uk)).run log =
      (fun r => (r, log)) <$> (initiator P).init uk := by
  simp [initiatorSim, initiator]

omit [DecidableEq PQPK] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K] in
lemma run_initiatorSim_output [Inhabited F] (pk : G) (x : F)
    (st : InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x) ((initiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK)
      (K := K) P).output st)).run log =
      (fun r => (r, log)) <$> (initiator P).output st := by
  rcases st with p | ctx | k <;> simp [initiatorSim, initiator]

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [SampleableType K] in
lemma run_recipientSim_output [Inhabited F] (pk : G) (x : F)
    (st : RecipientParameters F G PQPK PQSK S ⊕ K) (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x) ((recipientSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK)
      (K := K) P hasOPK).output st)).run log =
      (fun r => (r, log)) <$> (recipient P hasOPK).output st := by
  rcases st with p | k <;> simp [recipientSim, recipient]

/-! ## The same statements for the parties of the two schemes

The environments of the two runs mention the parties through `(uakeInitiator …).T` and
`(uakeInitiatorSim …).T`. These restatements keep the parties in that form, which the proofs of
the single-query equations need. -/

omit [DecidableEq PQPK] [SampleableType K] in
lemma simT_run_init [Inhabited F] (pk : G) (x : F) (tk : RecipientIdentity F G S)
    (htk : tk.ikB = (pk, x)) (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x)
      ((uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) (K := K) P msg hasOPK
        pk).T.init (scrubId tk))).run log =
      (fun r => (scrubInit r, initLog r ++ log)) <$> (uakeInitiator P msg hasOPK).T.init tk :=
  run_recipientSim_init P hasOPK pk x tk htk log

omit [DecidableEq PQPK] [SampleableType K] in
lemma simT_run_step [Inhabited F] (pk : G) (x : F)
    (st : RecipientParameters F G PQPK PQSK S ⊕ K)
    (hst : ∀ p, st = Sum.inl p → p.ikB = (pk, x))
    (w : Message G PQPK CT S C IdC IdK) (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x)
      ((uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) (K := K) P msg hasOPK
        pk).T.step (scrubState st) w)).run log =
      (fun r => (r, log)) <$> (uakeInitiator P msg hasOPK).T.step st w :=
  run_recipientSim_step P hasOPK pk x st hst w log

omit [DecidableEq PQPK] [SampleableType K] in
lemma simT_run_output [Inhabited F] (pk : G) (x : F)
    (st : RecipientParameters F G PQPK PQSK S ⊕ K) (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x)
      ((uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) (K := K) P msg hasOPK
        pk).T.output st)).run log =
      (fun r => (r, log)) <$> (uakeInitiator P msg hasOPK).T.output st :=
  run_recipientSim_output P hasOPK pk x st log

omit [DecidableEq PQPK] [SampleableType K] in
lemma simU_run_init [Inhabited F] (pk : G) (x : F) (uk : InitiatorParameters F G Msg)
    (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x)
      ((uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) (K := K) P msg hasOPK
        pk).U.init uk)).run log =
      (fun r => (r, log)) <$> (uakeInitiator P msg hasOPK).U.init uk :=
  run_initiatorSim_init P pk x uk log

omit [DecidableEq PQPK] [SampleableType K] in
lemma simU_run_step [Inhabited F] (pk : G) (x : F)
    (st : InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (w : Message G PQPK CT S C IdC IdK) (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x)
      ((uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) (K := K) P msg hasOPK
        pk).U.step st w)).run log =
      (fun r => (r, log)) <$> (uakeInitiator P msg hasOPK).U.step st w :=
  run_initiatorSim_step P pk x st w log

omit [DecidableEq PQPK] [SampleableType K] in
lemma simU_run_output [Inhabited F] (pk : G) (x : F)
    (st : InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    (log : List (SignatureInput G PQPK)) :
    (simulateQ (jointOr P pk x)
      ((uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) (K := K) P msg hasOPK
        pk).U.output st)).run log =
      (fun r => (r, log)) <$> (uakeInitiator P msg hasOPK).U.output st :=
  run_initiatorSim_output P pk x st log

lemma filterMap_set_of_eq {α β : Type} (g : α → Option β) (l : List α) (i : ℕ) (a a' : α)
    (hi : l[i]? = some a) (h : g a' = g a) : (l.set i a').filterMap g = l.filterMap g := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b l ih =>
    cases i with
    | zero =>
      simp only [List.length_cons, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, getElem?_pos,
          List.getElem_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [List.set_cons_zero, List.filterMap_cons, h]
    | succ i =>
      simp at hi
      simp only [List.set_cons_succ, List.filterMap_cons, ih i hi]

omit [DecidableEq PQPK] [SampleableType K] in
/-- Replacing a session by one whose transcript has the same bundle does not change the signing
log. -/
lemma signedLog_set [Inhabited F] (tk : RecipientIdentity F G S)
    (env : Env (uakeInitiator P msg hasOPK)) {sid : ℕ} {t : TSession (uakeInitiator P msg hasOPK)}
    (hs : env.tSessions[sid]? = some t) (t' : TSession (uakeInitiator P msg hasOPK))
    (h : transcriptBundle t'.transcript = transcriptBundle t.transcript) (c : ℕ)
    (ch : Session (uakeInitiator P msg hasOPK).U.State (Message G PQPK CT S C IdC IdK))
    (d : Bool) :
    signedLog P msg hasOPK tk ⟨c, ch, d, env.tSessions.set sid t'⟩ =
      signedLog P msg hasOPK tk env := by
  simp only [signedLog, List.filterMap_map]
  rw [filterMap_set_of_eq _ env.tSessions sid t t' hs (by simpa using h)]

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [SampleableType K] in
/-- A step of Bob's party never leaves a state that holds the identity secret, and never ends
with `complete`. -/
lemma recipient_step_state (st : RecipientParameters F G PQPK PQSK S ⊕ K)
    (w : Message G PQPK CT S C IdC IdK) :
    ∀ r ∈ support ((recipient P hasOPK).step st w),
      (∀ st' w' d, r = .acceptAndSend st' w' d → ∃ k, st' = Sum.inr k) ∧
        ∀ st', r ≠ .complete st' := by
  intro r hr
  have hrej : ∀ st' : (recipient P hasOPK).State,
      (Party.StepResult.reject : Party.StepResult _ (Message G PQPK CT S C IdC IdK)) ≠
        .complete st' := fun _ h => by cases h
  rcases st with p | k
  · rcases w with b | im | conf
    · simp only [recipient, MonadAttach.support_pure] at hr
      subst hr
      exact ⟨by simp, hrej⟩
    · simp only [recipient] at hr
      obtain ⟨o, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
      rcases o with _ | ctx
      · simp only [MonadAttach.support_pure] at hr; subst hr; exact ⟨by simp, hrej⟩
      · obtain ⟨conf, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
        simp only [MonadAttach.support_pure] at hr; subst hr
        exact ⟨fun st' w' d h => ⟨_, by cases h; rfl⟩, fun _ h => by cases h⟩
    · simp only [recipient, MonadAttach.support_pure] at hr
      subst hr
      exact ⟨by simp, hrej⟩
  · simp only [recipient, MonadAttach.support_pure] at hr
    subst hr
    exact ⟨by simp, hrej⟩

omit [AddCommGroup G] [DecidableEq G] [DecidableEq PQPK] in
lemma liftProbComp_sim {α : Type} (c : ProbComp α) :
    (ProbCompLift.ofMonadLift (OracleComp (Spec G PQPK S))).liftProbComp.toFun α c = up c := rfl

lemma liftProbComp_real {α : Type} (c : ProbComp α) :
    ProbCompRuntime.probComp.toProbCompLift.liftProbComp.toFun α c = c := rfl

omit [DecidableEq PQPK] [SampleableType K] in
/-- The simulation equation for one query. -/
theorem step_eq [Inhabited F] (pk : G) (x : F) (uk : InitiatorParameters F G Msg)
    (tk : RecipientIdentity F G S) (htk : tk.ikB = (pk, x))
    (t : (unifSpec + oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : Env (uakeInitiator P msg hasOPK)) (hI : SimInv P msg hasOPK pk x uk env) :
    (simulateQ (jointOr P pk x)
        (((simImpl P msg hasOPK pk (scrubId tk)) t).run (scrubEnv P msg hasOPK pk env))).run
      (signedLog P msg hasOPK tk env) =
    (fun z => ((z.1, scrubEnv P msg hasOPK pk z.2), signedLog P msg hasOPK tk z.2)) <$>
      ((realImpl P msg hasOPK tk) t).run env := by
  rcases t with n | op
  · simp [simImpl, realImpl, oracleImpl, liftProbComp_sim, liftProbComp_real, run_up]
  · cases op with
    | openT =>
      simp only [simImpl, realImpl, oracleImpl, QueryImpl.add_apply_inr, opImpl]
      simp only [add_apply_inr, Party.InitResult.opening, Party.InitResult.state, StateT.run_bind,
          StateT.run_monadLift, monadLift_self, bind_pure_comp, StateT.run_get, StateT.run_set,
          pure_bind, bind_map_left, simulateQ_bind, simT_run_init P msg hasOPK pk x tk htk,
          map_bind]
      erw [bind_map_left]
      refine bind_congr fun r => ?_
      erw [StateT.run_pure, StateT.run_pure]
      rcases r with ⟨st, w⟩ | ⟨st⟩
      · cases w <;> simp [scrubEnv, signedLog, initLog, scrubInit, recordOpt, recordOne,
          transcriptBundle]
      · simp [scrubEnv, signedLog, initLog, scrubInit, recordOpt, transcriptBundle]
    | stepT sid w =>
      simp only [simImpl, realImpl, oracleImpl, QueryImpl.add_apply_inr, opImpl]
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [add_apply_inr, pure_bind, scrubEnv, StateT.run_bind, StateT.run_get,
          List.getElem?_map, hs, Option.map_none]
        erw [StateT.run_pure, StateT.run_pure]
        simp
      · rcases hk : t.key with _ | key
        · have hsess := hI.sessions t (List.mem_of_getElem? hs)
          have hst := hsess.2
          obtain ⟨b, c, es, hent⟩ := hsess.1
          simp only [add_apply_inr, pure_bind, scrubEnv, StateT.run_bind, StateT.run_get,
              List.getElem?_map, hs, Option.map_some, hk, StateT.run_monadLift, monadLift_self,
              bind_pure_comp, bind_map_left, simulateQ_bind,
              simT_run_step P msg hasOPK pk x t.state hst w, map_bind]
          erw [bind_map_left]
          refine bind_congr_of_forall_mem_support _ fun r hr => ?_
          obtain ⟨hacc, hcomp⟩ := recipient_step_state P hasOPK t.state w r hr
          rcases r with ⟨st', w', done⟩ | st' | _
          · obtain ⟨k, rfl⟩ := hacc st' w' done rfl
            cases done
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind]
              erw [StateT.run_pure, StateT.run_pure]
              have hsl := signedLog_set P msg hasOPK tk env hs
                ⟨Sum.inr k, (recordOne (recordOne t.transcript w env.clock).1 w'
                  (recordOne t.transcript w env.clock).2).1, none, t.revealed⟩
                (by simp [transcriptBundle, recordOne, hent])
                (recordOne (recordOne t.transcript w env.clock).1 w'
                  (recordOne t.transcript w env.clock).2).2 env.challenge env.challengeDone
              simp [hsl, List.map_set, scrubState]
            · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
                bind_pure_comp, StateT.run_set, pure_bind, bind_map_left, simulateQ_bind,
                simT_run_output P msg hasOPK pk x, map_bind]
              refine bind_congr fun key' => ?_
              erw [StateT.run_pure, StateT.run_pure]
              have hsl := signedLog_set P msg hasOPK tk env hs
                ⟨Sum.inr k, (recordOne (recordOne t.transcript w env.clock).1 w'
                  (recordOne t.transcript w env.clock).2).1, key', t.revealed⟩
                (by simp [transcriptBundle, recordOne, hent])
                (recordOne (recordOne t.transcript w env.clock).1 w'
                  (recordOne t.transcript w env.clock).2).2 env.challenge env.challengeDone
              simp [hsl, List.map_set, scrubState]
          · exact absurd rfl (hcomp st')
          · simp only
            erw [StateT.run_pure, StateT.run_pure]
            simp
        · simp only [add_apply_inr, pure_bind, scrubEnv, StateT.run_bind, StateT.run_get,
            List.getElem?_map, hs, Option.map_some, hk]
          erw [StateT.run_pure, StateT.run_pure]
          simp
    | revealT sid =>
      simp only [simImpl, realImpl, oracleImpl, QueryImpl.add_apply_inr, opImpl]
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [add_apply_inr, scrubEnv, StateT.run_bind, StateT.run_get, pure_bind,
          List.getElem?_map, hs, Option.map_none]
        erw [StateT.run_pure, StateT.run_pure]
        simp
      · rcases hk : t.key with _ | key
        · simp only [add_apply_inr, scrubEnv, StateT.run_bind, StateT.run_get, pure_bind,
            List.getElem?_map, hs, Option.map_some, hk]
          erw [StateT.run_pure, StateT.run_pure]
          simp
        · simp only [add_apply_inr, scrubEnv, StateT.run_bind, StateT.run_get, pure_bind,
            List.getElem?_map, hs, Option.map_some, hk, StateT.run_set]
          erw [StateT.run_pure, StateT.run_pure]
          have hsl := signedLog_set P msg hasOPK tk env hs
            ⟨t.state, t.transcript, some key, true⟩ (by simp) env.clock env.challenge
            env.challengeDone
          simp [hsl, List.map_set, scrubState]
    | stepChallenge w =>
      simp only [simImpl, realImpl, oracleImpl, QueryImpl.add_apply_inr, opImpl]
      by_cases hd : env.challengeDone = true
      · simp only [add_apply_inr, scrubEnv, hd, StateT.run_bind, StateT.run_get, pure_bind,
          ↓reduceIte]
        erw [StateT.run_pure, StateT.run_pure]
        simp [hd]
      · have hd' : env.challengeDone = false := by simpa using hd
        simp only [add_apply_inr, scrubEnv, hd, StateT.run_bind, StateT.run_get, pure_bind,
            Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self, bind_pure_comp,
            bind_map_left, simulateQ_bind, map_bind]
        erw [simU_run_step P msg hasOPK pk x env.challenge.state w]
        erw [bind_map_left]
        refine bind_congr fun r => ?_
        rcases r with ⟨st', w', done⟩ | st' | _
        · simp only [StateT.run_bind, StateT.run_set, pure_bind]
          erw [StateT.run_pure, StateT.run_pure]
          simp [signedLog]
          rfl
        · simp only [StateT.run_bind, StateT.run_set, pure_bind]
          erw [StateT.run_pure, StateT.run_pure]
          simp [signedLog]
          rfl
        · simp only
          erw [StateT.run_pure, StateT.run_pure]
          simp [hd']

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [SampleableType K] in
/-- What Bob's `init` returns: his bundle and a state that holds his identity. -/
lemma recipient_init_shape (tk : RecipientIdentity F G S) :
    ∀ r ∈ support ((recipient P hasOPK).init tk),
      ∃ (p : RecipientParameters F G PQPK PQSK S) (b : PreKeyBundle G PQPK S IdC IdK),
        r = .speakFirst (Sum.inl p) (.bundle b) ∧ p.ikB = tk.ikB := by
  intro r hr
  simp only [recipient] at hr
  obtain ⟨opkB, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
  obtain ⟨pqpkB, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
  obtain ⟨bd, -, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
  simp only [support_pure] at hr
  exact ⟨_, bd, hr, rfl⟩

omit [DecidableEq PQPK] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K] in
/-- A successful `initiate` verified both signatures. -/
lemma initiate_verified (p : InitiatorParameters F G Msg) (b : PreKeyBundle G PQPK S IdC IdK)
    (r) (hr : some r ∈ support (initiate P p b)) : b.ikB = p.ikB ∧ Verified P p.ikB b := by
  unfold initiate at hr
  by_cases hik : b.ikB ≠ p.ikB
  · simp [hik] at hr
  · have hik' : b.ikB = p.ikB := not_not.1 hik
    refine ⟨hik', ?_⟩
    simp only [hik, ite_false] at hr
    obtain ⟨o₁, ho₁, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
    obtain ⟨o₂, ho₂, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
    by_cases hok : (o₁ && o₂) = true
    · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hok
      subst h1; subst h2
      exact ⟨ho₁, ho₂⟩
    · simp [hok] at hr

omit [DecidableEq PQPK] [DecidableEq IdC] [DecidableEq IdK] [SampleableType K] in
/-- A step of Alice's party from her initial state accepts only a bundle whose signatures
verified. -/
lemma initiator_step_inl (uk : InitiatorParameters F G Msg) (w : Message G PQPK CT S C IdC IdK) :
    ∀ r ∈ support ((initiator P).step (Sum.inl uk) w), r ≠ Party.StepResult.reject →
      ∃ b, w = Message.bundle b ∧ Verified P uk.ikB b := by
  intro r hr hne
  rcases w with b | im | conf
  · simp only [initiator] at hr
    obtain ⟨o, ho, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
    rcases o with _ | ⟨im, ctx⟩
    · simp only [MonadAttach.support_pure] at hr; exact absurd hr hne
    · exact ⟨b, rfl, (initiate_verified P uk b _ ho).2⟩
  · simp only [initiator, MonadAttach.support_pure] at hr; exact absurd hr hne
  · simp only [initiator, MonadAttach.support_pure] at hr; exact absurd hr hne

omit [DecidableEq PQPK] [SampleableType K] in
/-- Replacing one session by a session whose transcript extends the old one and whose state
holds Bob's identity key pair keeps the invariant. -/
lemma simInv_set_session [Inhabited F] {pk : G} {x : F} {uk : InitiatorParameters F G Msg}
    {env : Env (uakeInitiator P msg hasOPK)} (hI : SimInv P msg hasOPK pk x uk env) {sid : ℕ}
    {t : TSession (uakeInitiator P msg hasOPK)} (hs : env.tSessions[sid]? = some t)
    (t' : TSession (uakeInitiator P msg hasOPK))
    (ext : List (Message G PQPK CT S C IdC IdK × ℕ))
    (hext : t'.transcript.entries = t.transcript.entries ++ ext)
    (hst : ∀ p : RecipientParameters F G PQPK PQSK S,
      t'.state = (Sum.inl p : RecipientParameters F G PQPK PQSK S ⊕ K) → p.ikB = (pk, x))
    (c : ℕ) (d : Bool) :
    SimInv P msg hasOPK pk x uk ⟨c, env.challenge, d, env.tSessions.set sid t'⟩ := by
  refine ⟨hI.pinned, ?_, hI.challenge⟩
  intro s hs'
  rcases List.mem_or_eq_of_mem_set hs' with hs' | rfl
  · exact hI.sessions s hs'
  · obtain ⟨⟨b, c', es, he⟩, -⟩ := hI.sessions t (List.mem_of_getElem? hs)
    exact ⟨⟨b, c', es ++ ext, by rw [hext, he]; rfl⟩, hst⟩

omit [DecidableEq PQPK] [SampleableType K] in
/-- The same for a change of the clock and the flag only, with the sessions unchanged. -/
lemma simInv_clock [Inhabited F] {pk : G} {x : F} {uk : InitiatorParameters F G Msg}
    {env : Env (uakeInitiator P msg hasOPK)} (hI : SimInv P msg hasOPK pk x uk env)
    (c : ℕ) (d : Bool) :
    SimInv P msg hasOPK pk x uk ⟨c, env.challenge, d, env.tSessions⟩ :=
  ⟨hI.pinned, hI.sessions, hI.challenge⟩

omit [DecidableEq PQPK] [SampleableType K] in
/-- Every oracle query keeps the invariant. -/
theorem simInv_step [Inhabited F] (pk : G) (x : F) (uk : InitiatorParameters F G Msg)
    (tk : RecipientIdentity F G S) (htk : tk.ikB = (pk, x))
    (t : (unifSpec + oracleSpec K (Message G PQPK CT S C IdC IdK)).Domain)
    (env : Env (uakeInitiator P msg hasOPK)) (hI : SimInv P msg hasOPK pk x uk env) :
    ∀ z ∈ support (((realImpl P msg hasOPK tk) t).run env), SimInv P msg hasOPK pk x uk z.2 := by
  intro z hz
  rcases t with n | op
  · simp only [add_apply_inl, realImpl, oracleImpl, HasQuery.toQueryImpl_apply,
      HasQuery.instOfMonadLift_query, QueryImpl.add_apply_inl, StateT.run_monadLift, monadLift_self,
      bind_pure_comp, MonadAttach.support_map, Set.mem_image, MonadAttach.mem_support] at hz
    obtain ⟨a, -, rfl⟩ := hz
    exact hI
  · cases op with
    | openT =>
      simp only [realImpl] at hz
      rw [oracleImpl_openT_run, mem_support_bind_iff] at hz
      obtain ⟨r, hr, hz⟩ := hz
      have hinit : (uakeInitiator P msg hasOPK).T.init tk = (recipient P hasOPK).init tk := rfl
      rw [hinit] at hr
      obtain ⟨p, b, rfl, hp⟩ := recipient_init_shape P hasOPK tk r hr
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨hI.pinned, ?_, hI.challenge⟩
      intro s hs
      simp only [Env.openNext, Party.InitResult.opening, recordOpt, recordOne, List.nil_append,
        Party.InitResult.state, List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | rfl
      · exact hI.sessions s hs
      · refine ⟨⟨b, env.clock, [], rfl⟩, ?_⟩
        intro p' hp'
        obtain rfl := Sum.inl.inj hp'
        rw [hp, htk]
    | stepT sid w =>
      simp only [realImpl, oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [add_apply_inr, pure_bind, StateT.run_bind, StateT.run_get, hs,
          MonadAttach.mem_support] at hz
        subst hz
        exact hI
      · rcases hk : t.key with _ | key
        · have hsess := hI.sessions t (List.mem_of_getElem? hs)
          simp only [add_apply_inr, pure_bind, StateT.run_bind, StateT.run_get, hs, hk,
              StateT.run_monadLift, monadLift_self, bind_pure_comp, bind_map_left,
              MonadAttach.support_bind, MonadAttach.mem_support, Set.mem_iUnion, exists_prop] at hz
          obtain ⟨i, hi, hz⟩ := hz
          have hi' : i ∈ support ((recipient P hasOPK).step t.state w) := hi
          obtain ⟨hacc, hcomp⟩ := recipient_step_state P hasOPK t.state w i hi'
          rcases i with ⟨st', w', done⟩ | st' | _
          · obtain ⟨k, rfl⟩ := hacc st' w' done rfl
            cases done
            · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
                pure_bind] at hz
              erw [StateT.run_pure] at hz
              simp only [MonadAttach.canReturn_pure_iff] at hz
              subst hz
              exact simInv_set_session P msg hasOPK hI hs _
                [(w, env.clock), (w', env.clock + 1)] (by simp [recordOne])
                (fun p hp => by cases hp) _ _
            · simp only [↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
                bind_pure_comp, StateT.run_set, pure_bind, bind_map_left,
                MonadAttach.canReturn_bind_iff] at hz
              obtain ⟨key', -, hz⟩ := hz
              erw [StateT.run_pure] at hz
              simp only [MonadAttach.canReturn_pure_iff] at hz
              subst hz
              exact simInv_set_session P msg hasOPK hI hs _
                [(w, env.clock), (w', env.clock + 1)] (by simp [recordOne])
                (fun p hp => by cases hp) _ _
          · exact absurd rfl (hcomp st')
          · simp only at hz
            erw [StateT.run_pure] at hz
            simp only [MonadAttach.canReturn_pure_iff] at hz
            subst hz
            exact hI
        · simp only [add_apply_inr, pure_bind, StateT.run_bind, StateT.run_get, hs, hk,
            MonadAttach.mem_support] at hz
          subst hz
          exact hI
    | revealT sid =>
      simp only [realImpl, oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      rcases hs : env.tSessions[sid]? with _ | t
      · simp only [add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind, hs,
          MonadAttach.mem_support] at hz
        erw [StateT.run_pure] at hz
        simp only [MonadAttach.canReturn_pure_iff] at hz
        subst hz
        exact hI
      · rcases hk : t.key with _ | key
        · simp only [add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind, hs, hk,
            MonadAttach.mem_support] at hz
          erw [StateT.run_pure] at hz
          simp only [MonadAttach.canReturn_pure_iff] at hz
          subst hz
          exact hI
        · simp only [add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind, hs, hk,
            StateT.run_set, MonadAttach.mem_support] at hz
          erw [StateT.run_pure] at hz
          simp only [MonadAttach.canReturn_pure_iff] at hz
          subst hz
          exact simInv_set_session P msg hasOPK hI hs
            ⟨t.state, t.transcript, some key, true⟩ [] (by simp)
            (fun p hp => (hI.sessions t (List.mem_of_getElem? hs)).2 p hp) _ _
    | stepChallenge w =>
      simp only [realImpl, oracleImpl, QueryImpl.add_apply_inr, opImpl] at hz
      by_cases hd : env.challengeDone = true
      · simp only [add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind, hd, ↓reduceIte,
          MonadAttach.mem_support] at hz
        erw [StateT.run_pure] at hz
        simp only [MonadAttach.canReturn_pure_iff] at hz
        subst hz
        exact hI
      · simp only [add_apply_inr, StateT.run_bind, StateT.run_get, pure_bind, hd,
          Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self, bind_pure_comp,
          bind_map_left, MonadAttach.support_bind, MonadAttach.mem_support, Set.mem_iUnion,
          exists_prop] at hz
        obtain ⟨i, hi, hz⟩ := hz
        rcases i with ⟨st', w', done⟩ | st' | _
        · simp only [StateT.run_bind, StateT.run_set, pure_bind] at hz
          erw [StateT.run_pure] at hz
          simp only [MonadAttach.canReturn_pure_iff] at hz
          subst hz
          refine ⟨hI.pinned, hI.sessions, ?_⟩
          rcases hI.challenge with ⟨hst, hen⟩ | ⟨b, c, es, hent, hv⟩
          · have hi' : Party.StepResult.acceptAndSend st' w' done ∈
                support ((initiator P).step (Sum.inl uk) w) := by
              rw [hst] at hi
              exact hi
            obtain ⟨b, rfl, hv⟩ := initiator_step_inl P uk w _ hi' (fun h => by cases h)
            right
            exact ⟨b, env.clock, [(w', env.clock + 1)], by simp [recordOne, hen],
              by rw [← hI.pinned]; exact hv⟩
          · right
            exact ⟨b, c, es ++ [(w, env.clock), (w', env.clock + 1)], by simp [recordOne, hent], hv⟩
        · simp only [StateT.run_bind, StateT.run_set, pure_bind] at hz
          erw [StateT.run_pure] at hz
          simp only [MonadAttach.canReturn_pure_iff] at hz
          subst hz
          refine ⟨hI.pinned, hI.sessions, ?_⟩
          rcases hI.challenge with ⟨hst, hen⟩ | ⟨b, c, es, hent, hv⟩
          · have hi' : Party.StepResult.complete st' ∈
                support ((initiator P).step (Sum.inl uk) w) := by
              rw [hst] at hi
              exact hi
            obtain ⟨b, rfl, hv⟩ := initiator_step_inl P uk w _ hi' (fun h => by cases h)
            right
            exact ⟨b, env.clock, [], by simp [recordOne, hen],
              by rw [← hI.pinned]; exact hv⟩
          · right
            exact ⟨b, c, es ++ [(w, env.clock)], by simp [recordOne, hent], hv⟩
        · simp only at hz
          erw [StateT.run_pure] at hz
          simp only [MonadAttach.canReturn_pure_iff] at hz
          subst hz
          exact hI

omit [DecidableEq PQPK] [SampleableType K] in
/-- The simulation equation, from its single-query form. Simulating the reduction's oracle with
the joint oracles gives the real run with the environment scrubbed and the signing log read off
from the environment. -/
theorem sim_run_eq [Inhabited F] (pk : G) (x : F) (uk : InitiatorParameters F G Msg)
    (tk : RecipientIdentity F G S)
    (hstep : ∀ (t) (env : Env (uakeInitiator P msg hasOPK)),
      SimInv P msg hasOPK pk x uk env →
      (simulateQ (jointOr P pk x)
          (((simImpl P msg hasOPK pk (scrubId tk)) t).run (scrubEnv P msg hasOPK pk env))).run
        (signedLog P msg hasOPK tk env) =
      (fun z => ((z.1, scrubEnv P msg hasOPK pk z.2), signedLog P msg hasOPK tk z.2)) <$>
        ((realImpl P msg hasOPK tk) t).run env)
    (hinv : ∀ (t) (env : Env (uakeInitiator P msg hasOPK)),
      SimInv P msg hasOPK pk x uk env →
      ∀ z ∈ support (((realImpl P msg hasOPK tk) t).run env), SimInv P msg hasOPK pk x uk z.2)
    {α : Type} (oa : OracleComp (unifSpec + oracleSpec K (Message G PQPK CT S C IdC IdK)) α)
    (env : Env (uakeInitiator P msg hasOPK)) (hI : SimInv P msg hasOPK pk x uk env) :
    (simulateQ (jointOr P pk x)
        ((simulateQ (simImpl P msg hasOPK pk (scrubId tk)) oa).run
          (scrubEnv P msg hasOPK pk env))).run (signedLog P msg hasOPK tk env) =
      (fun z => ((z.1, scrubEnv P msg hasOPK pk z.2), signedLog P msg hasOPK tk z.2)) <$>
        (simulateQ (realImpl P msg hasOPK tk) oa).run env := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have hproj := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (realImpl P msg hasOPK tk)
    (QueryImpl.flattenStateT
      ((jointOr P pk x).mapStateTBase (simImpl P msg hasOPK pk (scrubId tk))))
    (SimInv P msg hasOPK pk x uk)
    (fun env => (scrubEnv P msg hasOPK pk env, signedLog P msg hasOPK tk env)) hinv
    (fun t env hI => by
      rw [QueryImpl.flattenStateT_mapStateTBase_apply_run, hstep t env hI, Functor.map_map]
      rfl)
    oa env hI
  rw [← hproj, Functor.map_map]
  rfl

omit [DecidableEq PQPK] [SampleableType K] in
/-- The initial environment of the challenge phase satisfies the invariant. -/
lemma simInv_init [Inhabited F] (pk : G) (x : F) (uk : InitiatorParameters F G Msg)
    (hpin : uk.ikB = pk) :
    SimInv P msg hasOPK pk x uk
      (⟨0, ⟨Sum.inl uk, ⟨[]⟩⟩, false, []⟩ : Env (uakeInitiator P msg hasOPK)) :=
  ⟨hpin, fun _ h => by simp at h, Or.inl ⟨rfl, rfl⟩⟩

omit [DecidableEq PQPK] [SampleableType K] in
/-- The challenge phase of the reduction, run against the joint oracles, is the real challenge
phase, with the environment scrubbed and the signing log read off from the final environment. -/
theorem sim_challenge_eq [Inhabited F] (pk : G) (x : F) (uk : InitiatorParameters F G Msg)
    (tk : RecipientIdentity F G S) (htk : tk.ikB = (pk, x)) (hpin : uk.ikB = pk)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    (simulateQ (jointOr P pk x)
      (challengeSession (ProbCompLift.ofMonadLift (OracleComp (Spec G PQPK S)))
        (proto := uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) P msg hasOPK pk)
        ⟨A.State, A.challenge, A.post⟩ uk (scrubId tk))).run [EncodeEC tk.spkB.1] =
    (fun r => ((⟨r.1.K0, r.1.challengeTr, r.1.oracleTrs⟩,
        (r.2.1, scrubEnv P msg hasOPK pk r.2.2.1, scrubId tk)),
          signedLog P msg hasOPK tk r.2.2.1)) <$>
      challengeSession ProbCompRuntime.probComp.toProbCompLift A uk tk := by
  have hinit : (uakeInitiator P msg hasOPK).U.init uk = pure (.waitForMsg (Sum.inl uk)) := rfl
  have hinitS : (uakeInitiatorSim (CT := CT) (C := C) (IdC := IdC) (IdK := IdK) P msg hasOPK
      pk).U.init uk = pure (.waitForMsg (Sum.inl uk)) := rfl
  unfold challengeSession
  erw [hinit, hinitS]
  simp only [pure_bind, simulateQ_bind, StateT.run_bind, Party.InitResult.opening,
    Party.InitResult.state, recordOpt, simulateQ_pure, map_bind]
  have h1 := sim_run_eq P msg hasOPK pk x uk tk (step_eq P msg hasOPK pk x uk tk htk)
    (simInv_step P msg hasOPK pk x uk tk htk) (A.challenge uk none)
    ⟨0, ⟨Sum.inl uk, ⟨[]⟩⟩, false, []⟩ (simInv_init P msg hasOPK pk x uk hpin)
  erw [h1]
  erw [bind_map_left]
  refine bind_congr fun a => ?_
  erw [simU_run_output P msg hasOPK pk x (S := S) a.2.challenge.state]
  erw [bind_map_left]
  refine bind_congr fun k0 => ?_
  erw [StateT.run_pure]
  simp only [map_pure, PFunctor.FreeM.pure_inj, Prod.mk.injEq, ChallengeResult.mk.injEq, true_and,
      and_true]
  exact ⟨rfl, by simp [scrubEnv, List.map_map, Function.comp_def]⟩

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
 [SampleableType K] in
lemma verify_eq_pure_true (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S),
      ∃ b, P.sig.verify pk m σ = pure b)
    {pk : G} {m : G ⊕ PQPK} {σ : S} (h : true ∈ support (P.sig.verify pk m σ)) :
    P.sig.verify pk m σ = pure true := by
  obtain ⟨b, hb⟩ := hverifyDet pk m σ
  rw [hb] at h ⊢
  simp only [MonadAttach.support_pure, Set.mem_singleton_iff, Bool.true_eq] at h
  rw [h]

omit [SampleableType K] in
/-- A real challenge phase that ends in the forgery event gives the reduction a valid signature on
a message that it never had signed. -/
lemma challenge_win [Inhabited F] (pk : G) (x : F) (uk : InitiatorParameters F G Msg)
    (tk : RecipientIdentity F G S) (htk : tk.ikB = (pk, x)) (hpin : uk.ikB = pk)
    (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (r : ChallengeResult (uakeInitiator P msg hasOPK) ×
      (A.State × Env (uakeInitiator P msg hasOPK) × RecipientIdentity F G S))
    (hr : r ∈ support (challengeSession ProbCompRuntime.probComp.toProbCompLift A uk tk))
    (hev : (r.1.K0.isSome &&
      (challengeBundle P msg hasOPK r.1).any fun b => !honestBundle P msg hasOPK r.2.2.2 r.1 b) =
        true) :
    P.sig.verify pk (forgery tk r.1.challengeTr).1 (forgery tk r.1.challengeTr).2 = pure true ∧
      (forgery tk r.1.challengeTr).1 ∉ signedLog P msg hasOPK tk r.2.2.1 := by
  have hinit : (uakeInitiator P msg hasOPK).U.init uk = pure (.waitForMsg (Sum.inl uk)) := rfl
  unfold challengeSession at hr
  erw [hinit] at hr
  simp only [pure_bind, Party.InitResult.opening, Party.InitResult.state, recordOpt] at hr
  obtain ⟨⟨st, env⟩, hse, hr1⟩ := (mem_support_bind_iff _ _ _).1 hr
  obtain ⟨k0, hk0, hr2⟩ := (mem_support_bind_iff _ _ _).1 hr1
  simp only [support_pure, Set.mem_singleton_iff] at hr2
  subst hr2
  have hI := OracleComp.simulateQ_run_preserves_inv_of_query (realImpl P msg hasOPK tk)
    (SimInv P msg hasOPK pk x uk) (simInv_step P msg hasOPK pk x uk tk htk) (A.challenge uk none)
    _ (simInv_init P msg hasOPK pk x uk hpin) (st, env) hse
  simp only at hI hk0 hev ⊢
  obtain ⟨hK0, hany⟩ := Bool.and_eq_true_iff.1 hev
  rcases hI.challenge with ⟨hst, hen⟩ | ⟨b, c, es, hent, hv⟩
  · exfalso
    have hk : k0 = none := by
      rw [hst] at hk0
      simpa [uakeInitiator, initiator] using hk0
    simp [hk] at hK0
  · have hcb : challengeBundle P msg hasOPK
        ⟨k0.join, env.challenge.transcript, env.tSessions.map (·.transcript)⟩ = some b := by
      simp [challengeBundle, transcriptBundle, hent]
    rw [hcb] at hany
    have hhon : honestBundle P msg hasOPK tk
        ⟨k0.join, env.challenge.transcript, env.tSessions.map (·.transcript)⟩ b = false := by
      simpa using hany
    have hfb : transcriptBundle env.challenge.transcript = some b := by
      simp [transcriptBundle, hent]
    by_cases hspk : b.spkB.1 = tk.spkB.1
    · simp only [honestBundle, hspk, decide_true, oracleBundles, List.filterMap_map,
        Function.comp_apply, List.any_filterMap, Bool.true_and, List.any_eq_false,
        Bool.not_eq_true] at hhon
      simp only [forgery, hfb, hspk, ↓reduceIte]
      refine ⟨verify_eq_pure_true P hverifyDet hv.2, ?_⟩
      simp only [signedLog, EncodeKEM, List.filterMap_map, Function.comp_apply, EncodeEC,
          List.mem_append, List.mem_reverse, List.mem_map, List.mem_filterMap, Sum.inr.injEq,
          List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, not_exists, not_and,
          forall_exists_index, and_imp]
      intro b' b1 hb1 hb' h
      have := hhon b1 hb1
      rw [hb'] at this
      simp only [decide_eq_false_iff_not] at this
      exact this h.symm
    · simp only [forgery, hfb, hspk, ↓reduceIte]
      refine ⟨verify_eq_pure_true P hverifyDet hv.1, ?_⟩
      simp only [signedLog, EncodeKEM, List.filterMap_map, Function.comp_apply, EncodeEC,
          List.mem_append, List.mem_reverse, List.mem_map, List.mem_filterMap, reduceCtorEq,
          and_false, exists_false, List.mem_cons, Sum.inl.injEq, List.not_mem_nil, or_false,
          false_or]
      exact hspk

omit [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq PQPK]
 [DecidableEq IdC] [DecidableEq IdK] in
/-- `forgery` does not read the identity key pair. -/
lemma forgery_ikB (ikB ikB' : G × F) (spkB : G × F) (σ : S)
    (tr : Transcript (Message G PQPK CT S C IdC IdK)) :
    forgery (⟨ikB, spkB, σ⟩ : RecipientIdentity F G S) tr =
      forgery (⟨ikB', spkB, σ⟩ : RecipientIdentity F G S) tr := rfl

omit [DecidableEq G] [DecidableEq PQPK] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
 [SampleableType K] in
/-- The signing log of `setupSim`. -/
lemma run_setupSim_bind [Inhabited F] (pk : G) (x : F) {β : Type}
    (f : InitiatorParameters F G Msg × RecipientIdentity F G S →
      OracleComp (Spec G PQPK S) β) :
    (simulateQ (jointOr P pk x) (setupSim (S := S) (PQPK := PQPK) P msg pk >>= f)).run [] =
      (do
        let ikA ← dhKeygen (F := F) P.gen
        let spkB ← dhKeygen (F := F) P.gen
        let σ ← P.sign pk x (EncodeEC spkB.1)
        (simulateQ (jointOr P pk x) (f (⟨ikA, pk, msg⟩, ⟨(pk, default), spkB, σ⟩))).run
          [EncodeEC spkB.1] : ProbComp (β × List (SignatureInput G PQPK))) := by
  simp [setupSim, simulateQ_bind, StateT.run_bind, run_up, run_signQ]

omit [SampleableType K] in
/-- The joint game against the reduction, as a computation of the real challenge phase followed
by the verification of the forgery. -/
lemma joint_exp_eq [Inhabited F] (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    SignatureAlg.jointUnforgeableExp P.sig (DH : F → G → G) (sigAdversary P msg hasOPK A) =
      (dhKeygen (F := F) P.gen >>= fun ikB => dhKeygen (F := F) P.gen >>= fun ikA =>
        dhKeygen (F := F) P.gen >>= fun spkB => P.sign ikB.1 ikB.2 (EncodeEC spkB.1) >>= fun σ =>
        challengeSession ProbCompRuntime.probComp.toProbCompLift A ⟨ikA, ikB.1, msg⟩
          ⟨ikB, spkB, σ⟩ >>= fun r =>
        P.verify ikB.1 (forgery (⟨ikB, spkB, σ⟩ : RecipientIdentity F G S) r.1.challengeTr).1
          (forgery (⟨ikB, spkB, σ⟩ : RecipientIdentity F G S) r.1.challengeTr).2 >>= fun ok =>
        pure (ok && decide ((forgery (⟨ikB, spkB, σ⟩ : RecipientIdentity F G S)
          r.1.challengeTr).1 ∉ signedLog P msg hasOPK ⟨ikB, spkB, σ⟩ r.2.2.1)) :
        ProbComp Bool) := by
  unfold SignatureAlg.jointUnforgeableExp
  refine bind_congr fun ikB => ?_
  rcases ikB with ⟨pk, x⟩
  simp only [sigAdversary]
  erw [run_setupSim_bind P msg pk x]
  simp only [bind_assoc]
  refine bind_congr fun ikA => bind_congr fun spkB => bind_congr fun σ => ?_
  simp only [simulateQ_bind, StateT.run_bind]
  have hsim := sim_challenge_eq P msg hasOPK pk x ⟨ikA, pk, msg⟩ ⟨(pk, x), spkB, σ⟩ rfl rfl A
  erw [hsim]
  simp only [bind_assoc, bind_map_left]
  refine bind_congr fun r => ?_
  erw [StateT.run_pure]
  simp only [pure_bind]
  rw [forgery_ikB (pk, default) (pk, x)]
  simp

/-- Two independent draws commute under an event. -/
lemma pr_swap {α β : Type} (mx : ProbComp α) (my : ProbComp β) (f : α → β → ProbComp Bool) :
    Pr{let y ← (mx >>= fun a => my >>= fun b => f a b)}[y = true] =
      Pr{let y ← (my >>= fun b => mx >>= fun a => f a b)}[y = true] := by
  simp only [map_bind]
  exact prEvent_bind_bind_swap_of_uniform _ _ _

omit [SampleableType K] in
/-- The signature forgery probability of any UAKE adversary is at most the advantage of the
reduction `sigAdversary` in the joint unforgeability game. -/
theorem sigForgeProb_le_advantage_sigAdversary [Inhabited F]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK))
    (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b) :
    sigForgeProb P msg hasOPK A ≤ (sigAdversary P msg hasOPK A).advantage.toReal := by
  have key : Pr{let y ← sigForgeExp P msg hasOPK A}[y = true] ≤
      (sigAdversary P msg hasOPK A).advantage := by
    unfold SignatureAlg.JointAdversary.advantage
    rw [joint_exp_eq P msg hasOPK A]
    unfold sigForgeExp challengePhase setup
    simp only [bind_assoc, pure_bind]
    refine le_of_eq_of_le (pr_swap _ _ _) ?_
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun ikB hikB => ?_
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun ikA hikA => ?_
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun spkB hspkB => ?_
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun σ hσ => ?_
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun r hr => ?_
    by_cases hev : (r.1.K0.isSome &&
        (challengeBundle P msg hasOPK r.1).any fun b => !honestBundle P msg hasOPK r.2.2.2 r.1 b) =
          true
    · obtain ⟨hver, hfresh⟩ := challenge_win P msg hasOPK ikB.1 ikB.2 ⟨ikA, ikB.1, msg⟩
        ⟨ikB, spkB, σ⟩ rfl rfl hverifyDet A r hr hev
      have hver' : P.verify ikB.1 (forgery (⟨ikB, spkB, σ⟩ : RecipientIdentity F G S)
          r.1.challengeTr).1 (forgery (⟨ikB, spkB, σ⟩ : RecipientIdentity F G S)
          r.1.challengeTr).2 = pure true := hver
      simp [hev, hver', hfresh]
    · have hev' : (r.1.K0.isSome &&
        (challengeBundle P msg hasOPK r.1).any fun b => !honestBundle P msg hasOPK r.2.2.2 r.1 b) =
          false := by simpa using hev
      simp [hev']
  exact ENNReal.toReal_mono (prEvent_ne_top _) key

end

end SigReduction

end Protocols.Models.PQXDH
