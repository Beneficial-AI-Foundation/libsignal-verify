/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.Basic
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import Protocols.ToMathlib
import Protocols.ToVCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.ProgramLogic.Relational.Quantitative

/-!
# PQXDH Modeled as a DF'17-style UAKE

Using our Lean model of PQXDH, we construct a unilaterally
authenticated key exchange scheme, as described in Dodis and Fiore 2017
(<https://eprint.iacr.org/2017/109>). A UAKE is a two-party protocol between parties U and
T, in which U and T derive a shared secret. UAKE security ensures that, if U
accepts the exchange, the shared secret is indistinguishable from random, and
T's messages sent to U are authentic.

The "unilateral" part of a UAKE means that its two parties play different
roles: The T party is authenticated, and UAKE security ensures that the
adversary cannot spoof its messages in an exchange. The U is unauthenticated,
and merely checks the T party's authenticity. For that reason, we instantiate
the protocol twice, once with Alice as T, and once with Bob as T. Note that
these two instantiations need slightly different shapes, due to the convention
from DF'17 that "T speaks last". In both cases, the initial message is from
Bob, so the T=Bob case is 3-round, with an extra confirmation message from Bob
(see bullet 1 of "Model simplifications" in `Protocols/PQXDH/Model/Basic.lean`) whereas the
T=Alice case is the standard 2-round protocol.

Model simplifications
* **Medium-term secrets as long-term:** The spec describes SPK and PQSPK as
  "changed periodically", but the UAKE security game only allows for permanent
  (via setup) and per-session (via init) keys. We model SPK (and its signature)
  as permanent, along with IK{A|B}.
* **No fallback KEM key:** We do not (currently) model the spec's last-resort
  KEM key (PQSPK). We generate a one-time KEM key (PQOPKᵢ) every time. We plan
  to extend the model to include the fallback branch in the future. Note that
  this is not necessarily a simple extension, since the fallback branch we omit
  is substantively weaker: According to Section 4.7 of the spec, compromising
  PQSPKB in a PQ setting retroactively compromises the session's SK in the
  fallback case, and Sections 4.2 and 4.3 note that replay becomes possible if
  a one-time key is omitted.
* **Key bundle as a message from Bob:** The PQXDH spec describes the key bundle
  as coming from a third party server. Since UAKE is a two-party protocol, we
  model it as coming from Bob instead.
* **KEM public key unconditionally included in AD:** The spec requires Bob's KEM
  public key to be included in AD "if pqkem does not incorporate [it] into the
  ciphertext." We unconditionally include it, which allows us to make no such
  assumption about the KEM.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

/-- The message type in the UAKE exchange. -/
inductive Message (G PQPK CT S C IdC IdK : Type) where
  /-- Bob's pre-key bundle -/
  | bundle : PreKeyBundle G PQPK S IdC IdK → Message G PQPK CT S C IdC IdK
  /-- Alice's message to Bob initiating the key exchange -/
  | initial : InitialMessage G CT C IdC IdK → Message G PQPK CT S C IdC IdK
  /-- Bob's confirmation message, if the exchange is accepted -/
  | confirmation : C → Message G PQPK CT S C IdC IdK
  deriving DecidableEq

/-- Alice's Party state machine, which internally uses the `initiate` function,
  traceable to the PQXDH spec, followed by the `confirm` function, which checks
  Bob's AEAD ciphertext (not in the spec). -/
def initiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party ProbComp (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
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

/-- Bob's Party state machine, which internally uses the `accept` and `publish`
  functions, traceable to the PQXDH spec, as well as sending a final AEAD
  message (not in the spec). -/
def recipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K
  init := fun idn => do
    let opkB ← genOPK P.gen hasOPK
    let pqpkB ← P.pqkem.keygen
    let p : RecipientParameters F G PQPK PQSK SPK SSK S :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => do
            /- DEVIATION FROM SPEC: UAKE requires T to speak last, sending an
              authenticated message if the exchange was accepted. This prevents
              a trivial attack where the attacker simply refrains from sending
              Alice's last message, so that ping-pong is vacuously false. We
              have Bob send the final message of the exchange here in order to
              satisfy this, whereas the spec stops at Bob receiving the
              message. -/
            let conf ← P.aead.encrypt ctx.kb ctx.ad ctx.msg
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

/-- UAKE scheme in which Bob plays the part of the authenticated party T and
  sends a final AEAD ciphertext to match the "T speaks last" convention from
  DF'17. -/
def uakeInitiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SPK Msg)
      (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  /- 3 messages sent:
    Bob's pre-key bundle → Alice's initiate message → Bob's confirmation message -/
  rounds := 3
  /- Generate long-term state using `setup`. -/
  setup := setup P msg
  /- Alice is unkeyed party -/
  U := initiator P
  /- Bob is authenticated party -/
  T := recipient P hasOPK

/-- Alice's Party state machine, which internally uses the `initiate` function,
  traceable to the PQXDH spec. -/
def initiatorNoConfirm [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party ProbComp (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiate P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr ctx.sk) (.initial im) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr SK => pure (some (some SK))
    | _ => pure none

/-- Bob's Party state machine, which internally uses the `publish` and `accept`
  functions, traceable to the PQXDH spec. -/
def recipientNoConfirm [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K
  init := fun idn => do
    let opkB ← genOPK P.gen hasOPK
    let pqpkB ← P.pqkem.keygen
    let p : RecipientParameters F G PQPK PQSK SPK SSK S :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => pure (.complete (.inr ctx.sk))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

/-- UAKE scheme in which Alice plays the part of the authenticated party T. -/
def uakeRecipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (RecipientIdentity F G SPK SSK S)
      (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) where
  /- 2 messages sent: Bob's pre-key bundle → Alice's initiate message -/
  rounds := 2
  /- Generate long-term state using `setup`. -/
  setup := Prod.swap <$> setup P msg
  /- Bob is unkeyed party -/
  U := recipientNoConfirm P hasOPK
  /- Alice is authenticated party -/
  T := initiatorNoConfirm P

/-- Bounds the number of sessions started by the adversary with its T oracle by
  bounding the number of openT queries. -/
def _root_.AKE.UAKE.Adversary.OpensAtMost {K UK TK W : Type}
    {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (q : ℕ) : Prop :=
  (∀ uk w, (A.challenge uk w).IsQueryBoundP (· matches Sum.inr .openT) q) ∧
    (∀ st k, (A.post st k).IsQueryBoundP (· matches Sum.inr .openT) q)

/-- KDF modeled as a PRF keyed by a bitstring (e.g., the output of the KEM). -/
def kdfPRF [SampleableType SS]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    PRFScheme SS (G × G × G × Option G) (K × K × K) where
  keygen := $ᵗ SS
  eval := fun ss q => P.kdf (q.1, q.2.1, q.2.2.1, q.2.2.2, ss)

/-- KDF modeled as a PRF keyed by a DH group element (e.g., the output of a DH
  key exchange). -/
def kdfPRFDH [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    PRFScheme F (G × G × Option G × SS) (K × K × K) where
  keygen := $ᵗ F
  eval := fun c q => P.kdf (q.1, q.2.1, c • P.gen, q.2.2.1, q.2.2.2)

end Protocols.PQXDH
