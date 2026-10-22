/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.WellFormedLemmas

/-!
# Games and Events for the PQXDH Security Hops

The challenge-phase game shared by the security hops, the derived
experiments (forgery, signature forgery, KEM-key guessing, and the
coin-flipped indistinguishability experiment), and the transcript-level
event predicates they use. The hop lemmas over these games live in the
sibling files of `SecurityLemmas/`; see `SecurityLemmas.lean` for the
overall map.

The definitions in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.PQXDH

noncomputable section

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- The pre-key bundle carried by a transcript's first message, if any. In
  the T=Bob scheme, a T-oracle session transcript begins with the bundle Bob
  published, and a completed challenge transcript begins with the bundle the
  initiator accepted (rejected messages are dropped from transcripts). -/
def transcriptBundle (tr : Transcript (Message G PQPK CT S C IdC IdK)) :
    Option (PreKeyBundle G PQPK S IdC IdK) :=
  match tr.entries.head? with
  | some (Message.bundle b, _) => some b
  | _ => none

/-- The global-clock timestamp of a transcript's first entry, if any. For a
  T-oracle session this is the time the session was opened; for the
  challenge transcript it is the time the initiator accepted a bundle. -/
def transcriptStart (tr : Transcript (Message G PQPK CT S C IdC IdK)) : Option ℕ :=
  tr.entries.head?.map Prod.snd

/-- The bundles published by the T-oracle sessions, in session order. -/
def oracleBundles (cr : ChallengeResult (uakeInitiator P msg hasOPK)) :
    List (PreKeyBundle G PQPK S IdC IdK) :=
  cr.oracleTrs.filterMap transcriptBundle

/-- The bundle accepted by the challenge session, if it accepted one. -/
def challengeBundle (cr : ChallengeResult (uakeInitiator P msg hasOPK)) :
    Option (PreKeyBundle G PQPK S IdC IdK) :=
  transcriptBundle cr.challengeTr

/-- True if every signed pair the initiator verifies in the bundle `b` was
  honestly produced by the challenger: the signed pre-key pair is the one
  created by `setup`, and the KEM pair was published by some T-oracle
  session. A completed challenge session whose accepted bundle fails this
  predicate yields a strong (SUF-CMA) signature forgery. -/
def honestBundle (tk : RecipientIdentity F G SPK SSK S)
    (cr : ChallengeResult (uakeInitiator P msg hasOPK))
    (b : PreKeyBundle G PQPK S IdC IdK) : Bool :=
  decide (b.spkB.1 = tk.spkB.1) && decide (b.spkSigB = tk.spkSigB) &&
    (oracleBundles P msg hasOPK cr).any fun b' =>
      decide (b.pqpkB.1 = b'.pqpkB.1) && decide (b.pqpkSigB = b'.pqpkSigB)

/-- The KEM-key bad event of the forgery branch: either two T-oracle
  sessions published the same KEM public key, or the challenge session
  accepted its bundle strictly before some T-oracle session carrying the
  same KEM public key was opened (i.e., the adversary predicted an honest
  KEM key before it was generated). Both are guessing events on
  `P.pqkem.keygen`. No cryptographic hypothesis of the security theorems
  excludes them, and a KEM with colliding or predictable public keys
  genuinely breaks UAKE security: a second session holding the same KEM key
  (and the same one-time key, when one is in use) accepts a replay of the
  challenge session's initial message, derives the same session key, and can
  be revealed without matching the challenge transcript. -/
def pqpkGuessed (cr : ChallengeResult (uakeInitiator P msg hasOPK)) : Bool :=
  !decide ((oracleBundles P msg hasOPK cr).map (·.pqpkB.1)).Nodup ||
    ((challengeBundle P msg hasOPK cr).any fun b =>
      (transcriptStart cr.challengeTr).any fun tc =>
        cr.oracleTrs.any fun tr =>
          ((transcriptBundle tr).any fun b' => decide (b.pqpkB.1 = b'.pqpkB.1)) &&
            (transcriptStart tr).any fun ti => decide (tc < ti))

/-- The challenge phase of the UAKE experiment against the T=Bob scheme: run
  `setup`, then the adversary's challenge stage with oracle access to copies
  of T. The challenge bit is independent of this phase, so the experiments
  below sample it themselves where needed; this matches `UAKE.Exp` up to
  commuting independent samples. -/
def challengePhase (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    ProbComp (ChallengeResult (uakeInitiator P msg hasOPK) ×
      (A.State × Env (uakeInitiator P msg hasOPK) × RecipientIdentity F G SPK SSK S)) := do
  let (uk, tk) ← setup P msg
  challengeSession ProbCompRuntime.probComp.toProbCompLift A uk tk

/-- Forgery experiment: the challenge session completed, but its transcript
  matches no T-oracle session, so the adversary spoofed a message from T. -/
def forgeExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (cr, _) ← challengePhase P msg hasOPK A
  return cr.K0.isSome && !isPingPong cr

/-- Probability of the forgery event. -/
def forgeProb (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  (Pr[= true | forgeExp P msg hasOPK A]).toReal

/-- Signature-forgery experiment: the challenge session completed, and some
  signed pair in the bundle it accepted was never produced by the
  challenger. -/
def sigForgeExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (cr, st) ← challengePhase P msg hasOPK A
  return cr.K0.isSome &&
    (challengeBundle P msg hasOPK cr).any fun b => !honestBundle P msg hasOPK st.2.2 cr b

/-- Probability of the signature-forgery event. -/
def sigForgeProb (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  (Pr[= true | sigForgeExp P msg hasOPK A]).toReal

/-- KEM-key guessing experiment: the bad event `pqpkGuessed` occurred during
  the challenge phase. -/
def pqpkGuessedExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (cr, _) ← challengePhase P msg hasOPK A
  return pqpkGuessed P msg hasOPK cr

/-- Probability of the KEM-key guessing event. -/
def pqpkGuessedProb (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  (Pr[= true | pqpkGuessedExp P msg hasOPK A]).toReal

/-- Residual forgery experiment: a forgery on an honestly signed bundle,
  with pairwise-distinct and unpredicted KEM keys. This is the event bounded
  by the forgery cores (Hop 5). -/
def forgeHonestGoodExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (cr, st) ← challengePhase P msg hasOPK A
  return cr.K0.isSome && !isPingPong cr &&
    ((challengeBundle P msg hasOPK cr).all fun b => honestBundle P msg hasOPK st.2.2 cr b) &&
    !pqpkGuessed P msg hasOPK cr

/-- Probability of the residual forgery event. -/
def forgeHonestGoodProb (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  (Pr[= true | forgeHonestGoodExp P msg hasOPK A]).toReal

/-- The UAKE experiment with the forgery branch's outright win replaced by a
  fair coin flip. Identical to `UAKE.Exp` on the other two branches. -/
def indistExp (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ProbComp Bool := do
  let (uk, tk) ← setup P msg
  let b ← $ᵗ Bool
  let (cr, st) ← challengeSession ProbCompRuntime.probComp.toProbCompLift A uk tk
  if cr.K0.isNone then
    finalize ProbCompRuntime.probComp.toProbCompLift A st cr b none
  else if !isPingPong cr then
    $ᵗ Bool
  else do
    let K1 ← some <$> ($ᵗ K)
    finalize ProbCompRuntime.probComp.toProbCompLift A st cr b K1

/-- The adversary's advantage over a fair coin in `indistExp`. -/
def indistAdvantage (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) : ℝ :=
  |(Pr[= true | indistExp P msg hasOPK A]).toReal - 1 / 2|

end

end Protocols.PQXDH
