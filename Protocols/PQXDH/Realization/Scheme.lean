/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.Defs
import Protocols.PQXDH.Realization.Kem

/-!
# The Full realization: PQXDH as a UAKE scheme on the extracted entry points

This file builds the Full realization: a Full core realization plus an explicitly synthetic
UAKE/AEAD wrapper. The core is the extracted handshake: Alice's step runs the extracted
`pqxdh_initiate` and Bob's runs the extracted `pqxdh_accept`, both through `liftResult` in
`RustOracleComp unifSpec`. A panic or a non-terminating call of extracted code is therefore a
fault, which the runtime counts as missing probability mass; it never becomes a rejection, an
absent output or a default value. A protocol error that the extracted code returns, such as
`InvalidMessage` for a non-canonical ephemeral key, is an ordinary value and the party rejects
the message.

## The wrapper

The UAKE notion of Dodis and Fiore needs more than the handshake, and the wrapper supplies it.
None of it is extracted code.

* **Bundle and identity checks.** Bob publishes his prekey bundle as a message, and Alice checks
  that the bundle names Bob's identity key, which she knows out of band, and verifies the two
  prekey signatures with the extracted `PublicKey::verify_signature`, as
  `process_prekey_bundle` does (`rust/protocol/src/session.rs:208-230`). The identity check
  stands for production's trusted-identity store.
* **One identity key.** Bob's identity key pair both signs his prekeys and performs the
  Diffie-Hellman exchange DH2, as in production. There is no separate signature key. Signatures
  are computed by the extracted `PrivateKey::calculate_signature` on the extracted serialization
  of each prekey (`rust/protocol/src/session_management.rs:883-890`), with a fresh draw of the
  generator state from `P.coins`; a fault in signing or verification is a fault of the run, and
  a signing error is a returned value after which Bob does not publish.
* **Synthetic AEAD messages.** Alice's initial message carries an AEAD ciphertext under the key
  `(syntheticAeadRoles keys).alice`; it models the specification's initial ciphertext. Production
  sends that ciphertext as the first Double Ratchet message under ratchet-derived keys, so this
  is not an extracted-code correspondence. Bob's confirmation, an AEAD ciphertext under
  `(syntheticAeadRoles keys).bob`, exists only in the model: the UAKE game needs the
  authenticated party to speak last.

## Keys and state

Every key pair is drawn from the ideal generators `P.ecKeygen` and `P.pqKeygen`; Alice's
generator state `R` is one draw from `P.coins` per session, kept in her state and threaded through
`pqxdh_initiate`. A rejected message leaves the state, and with it `R`, unchanged. Both completed
states keep the joint output `JointKeys` (root key, chain key with its index, post-quantum ratchet
key), the associated data and the exact inputs of the entry-point call. The UAKE output is the
root key only, which is the target of the existing game; the projection lemmas
`initiator_output_eq` and `recipient_output_eq` state that the output is the root key of the
stored joint output.

Two schemes are built. In `uakeInitiator` Bob is the authenticated party and sends the
confirmation; the security statements concern this scheme. In `uakeRecipient` Alice is the
authenticated party and the exchange has two messages; it is used for correctness only.

**Source**: `PQXDH/Aeneas/Full/UAKE/Defs.lean` of libsignal-docs-and-models, rebuilt. The
source's wrappers `runRaw`, `runRes` and `getRes`, its default-filled KEM and its signature
adapter `extractedSig` replace faults by `none` or by default values; none of them is ported.
The separate signature key, the comparison of key identifiers for the one-time prekey and the
`ProbComp` monad are changed as described above.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open Aeneas Aeneas.Std
open libsignal_protocol
open Protocols.Realization

namespace Protocols.PQXDH.Realization

noncomputable section

/-- Equality of public keys, decided classically: the wrapper compares keys and the UAKE game
compares messages. -/
scoped instance : DecidableEq ECPub := Classical.decEq _

/-- Equality of Kyber public keys, decided classically. -/
scoped instance : DecidableEq PQPub := Classical.decEq _

/-- Equality of byte slices, decided classically. -/
scoped instance : DecidableEq (Slice U8) := Classical.decEq _

variable {Rand Msg C IdC IdK : Type}

/-- Bob's prekey bundle: his identity key, signed prekey, Kyber prekey and optional one-time
prekey, with identifiers and the two signatures. -/
abbrev FullBundle (IdC IdK : Type) : Type := PreKeyBundle ECPub PQPub (Slice U8) IdC IdK

/-- Alice's initial message: her identity and ephemeral keys, the serialized Kyber ciphertext,
the identifiers of the prekeys she used and the synthetic AEAD ciphertext. -/
abbrev FullInitialMessage (C IdC IdK : Type) : Type := InitialMessage ECPub (Slice U8) C IdC IdK

/-- The messages of the UAKE exchange: the bundle, the initial message and the confirmation. -/
abbrev FullMessage (C IdC IdK : Type) : Type :=
  Message ECPub PQPub (Slice U8) (Slice U8) C IdC IdK

/-- The identity public key carried by a curve25519 key pair. -/
def identityKeyOf (kp : ECKeyPair) : IdKey := { public_key := kp.public_key }

/-- A curve25519 key pair as an identity key pair. -/
def identityKeyPairOf (kp : ECKeyPair) : IdKeyPair :=
  { identity_key := identityKeyOf kp, private_key := kp.private_key }

/-- Alice's long-term state: her identity key pair, Bob's identity key, which she knows out of
band, and the message of her synthetic ciphertext. -/
structure InitiatorParameters (Msg : Type) where
  /-- Alice's identity key pair. -/
  ikA : IdKeyPair
  /-- Bob's identity key, pinned. -/
  ikB : IdKey
  /-- The message of the synthetic initial ciphertext. -/
  msg : Msg

/-- Bob's long-term state: his identity key pair, which both signs and agrees, his signed prekey
pair and the result of signing it. -/
structure RecipientIdentity where
  /-- Bob's identity key pair. -/
  ikB : IdKeyPair
  /-- Bob's signed prekey pair. -/
  spkB : ECKeyPair
  /-- The result of signing the signed prekey: a signature, or the error that signing
  returned. -/
  spkSigB : core.result.Result (Slice U8) libsignal_core.curve.CurveError

/-- Bob's state for one session: his long-term keys, the signature of his signed prekey, and the
one-time and Kyber prekey pairs drawn for this session. -/
structure RecipientParameters where
  /-- Bob's identity key pair. -/
  ikB : IdKeyPair
  /-- Bob's signed prekey pair. -/
  spkB : ECKeyPair
  /-- The signature of the signed prekey. -/
  spkSigB : Slice U8
  /-- Bob's one-time prekey pair for this session, if any. -/
  opkB : Option ECKeyPair
  /-- Bob's Kyber prekey pair for this session. -/
  pqpkB : PQKeyPair

/-- What Alice keeps after her entry point succeeded: the exact inputs of the call, the generator
state she passed to it, the joint output, the associated data and her message. -/
structure AliceSession (Rand Msg : Type) where
  /-- The parameters of the call of the initiator's entry point. -/
  inputs : pqxdh.InitiatorParameters
  /-- The generator state passed to the call. -/
  coins : Rand
  /-- The joint output of the call. -/
  keys : JointKeys
  /-- The associated data `(IK_A, IK_B, PQPK_B)` of the synthetic ciphertexts. -/
  ad : ECPub × ECPub × PQPub
  /-- The message of the synthetic ciphertexts. -/
  msg : Msg

/-- What Bob keeps after his entry point succeeded and Alice's ciphertext decrypted: the exact
inputs of the call, the joint output, the associated data and the decrypted message. -/
structure BobSession (Msg : Type) where
  /-- The parameters of the call of the responder's entry point. -/
  inputs : pqxdh.RecipientParameters
  /-- The joint output of the call. -/
  keys : JointKeys
  /-- The associated data `(IK_A, IK_B, PQPK_B)` of the synthetic ciphertexts. -/
  ad : ECPub × ECPub × PQPub
  /-- The message decrypted from Alice's ciphertext. -/
  msg : Msg

/-- The extracted serialization of a curve25519 public key, the message of a signed-prekey
signature (`rust/core/src/curve.rs:122-131`). -/
def encodeEC (pk : ECPub) : RustOracleComp unifSpec (Slice U8) :=
  liftResult (libsignal_core.curve.PublicKey.serialize pk)

/-- The extracted serialization of a Kyber public key, the message of a Kyber-prekey signature
(`rust/protocol/src/kem.rs:346-351`). -/
def encodeKEM (pk : PQPub) : RustOracleComp unifSpec (Slice U8) :=
  liftResult (kem.Key.serialize kem.Public.Insts.Libsignal_protocolKemKeyKind pk)

/-- **Signing, faults kept.** Sign `m` with the private key `sk` by the extracted
`calculate_signature`, on a fresh draw of the generator state from `P.coins`. A panic or a
non-terminating call is a fault of the run; a returned error is returned. -/
def signBytes (P : Params Rand Msg C IdC IdK) (sk : ECPriv) (m : Slice U8) :
    RustOracleComp unifSpec (core.result.Result (Slice U8) libsignal_core.curve.CurveError) := do
  let r ← (liftM P.coins : RustOracleComp unifSpec Rand)
  let (res, _) ← liftResult (curve.PrivateKey.calculate_signature P.cryptoRngInst P.rngInst sk m r)
  pure res

/-- **Verification, faults kept.** Verify the signature `σ` on `m` under `pk` by the extracted
`verify_signature`. A panic or a non-terminating call is a fault of the run, never `false`. -/
def verifyBytes (pk : ECPub) (m σ : Slice U8) : RustOracleComp unifSpec Bool :=
  liftResult (libsignal_core.curve.PublicKey.verify_signature pk m σ)

/-- Long-term keys: Alice's identity key pair, Bob's identity key pair and Bob's signed prekey
pair, all from the ideal generator, and Bob's signature of his signed prekey with his identity
key. -/
def setup (P : Params Rand Msg C IdC IdK) (msg : Msg) :
    RustOracleComp unifSpec (InitiatorParameters Msg × RecipientIdentity) := do
  let ikA ← (liftM P.ecKeygen : RustOracleComp unifSpec ECKeyPair)
  let ikB ← (liftM P.ecKeygen : RustOracleComp unifSpec ECKeyPair)
  let spkB ← (liftM P.ecKeygen : RustOracleComp unifSpec ECKeyPair)
  let spkBytes ← encodeEC spkB.public_key
  let spkSigB ← signBytes P ikB.private_key spkBytes
  pure ({ ikA := identityKeyPairOf ikA, ikB := identityKeyOf ikB, msg := msg },
    { ikB := identityKeyPairOf ikB, spkB := spkB, spkSigB := spkSigB })

/-- Bob's bundle for one session: he signs his Kyber prekey with his identity key and publishes
his public keys with their identifiers. A signing error is returned and nothing is published.
In production the bundle comes from a server; the UAKE game has two parties, so Bob sends it. -/
def publish (P : Params Rand Msg C IdC IdK) (p : RecipientParameters) :
    RustOracleComp unifSpec
      (core.result.Result (FullBundle IdC IdK) libsignal_core.curve.CurveError) := do
  let pqBytes ← encodeKEM p.pqpkB.public_key
  let sig ← signBytes P p.ikB.private_key pqBytes
  match sig with
  | .Err e => pure (.Err e)
  | .Ok pqpkSigB =>
      pure (.Ok
        { ikB := p.ikB.identity_key.public_key
          spkB := (p.spkB.public_key, P.idEC p.spkB.public_key)
          spkSigB := p.spkSigB
          pqpkB := (p.pqpkB.public_key, P.idKEM p.pqpkB.public_key)
          pqpkSigB := pqpkSigB
          opkB := p.opkB.map fun opk => (opk.public_key, P.idEC opk.public_key) })

/-- Draw a one-time prekey pair when `hasOPK` holds. -/
def genOPK (P : Params Rand Msg C IdC IdK) (hasOPK : Bool) : ProbComp (Option ECKeyPair) :=
  if hasOPK then some <$> P.ecKeygen else pure none

/-- **Alice's step on a bundle.** She checks Bob's identity key, then the signature of the signed
prekey, then the signature of the Kyber prekey, stopping at the first failure as
`process_prekey_bundle` does (`rust/protocol/src/session.rs:208-230`): the Kyber key is not
serialized when the first signature fails. She then draws her ephemeral key pair and runs the
initiator's entry point on her generator state `R`. On success she encrypts her message under the
synthetic key and returns her initial message, her session and the new generator state. Any
failed check or returned protocol error gives `none`; a fault of extracted code is a fault of the
run. -/
def initiate (P : Params Rand Msg C IdC IdK) (E : EntryPoints Rand) (p : InitiatorParameters Msg)
    (R : Rand) (b : FullBundle IdC IdK) :
    RustOracleComp unifSpec
      (Option (FullInitialMessage C IdC IdK × AliceSession Rand Msg × Rand)) := do
  if b.ikB ≠ p.ikB.public_key then return none
  let spkBytes ← encodeEC b.spkB.1
  let okSPK ← verifyBytes b.ikB spkBytes b.spkSigB
  if !okSPK then return none
  let pqBytes ← encodeKEM b.pqpkB.1
  let okPQ ← verifyBytes b.ikB pqBytes b.pqpkSigB
  if !okPQ then return none
  let ekA ← (liftM P.ecKeygen : RustOracleComp unifSpec ECKeyPair)
  let ip : pqxdh.InitiatorParameters :=
    { our_identity_key_pair := p.ikA
      our_ephemeral_key_pair := ekA
      their_identity_key := { public_key := b.ikB }
      their_signed_pre_key := b.spkB.1
      their_one_time_pre_key := b.opkB.map Prod.fst
      their_ratchet_key := b.spkB.1
      their_kyber_pre_key := b.pqpkB.1
      self_session := false }
  let (res, R') ← liftResult (E.initiate P.rngInst P.cryptoRngInst ip R)
  match res with
  | .Err _ => return none
  | .Ok ag =>
      let keys := JointKeys.ofHandshakeKeys ag.keys
      let ad := (p.ikA.identity_key.public_key, b.ikB, b.pqpkB.1)
      let ctxt ← (liftM (P.aead.encrypt (syntheticAeadRoles keys).alice ad p.msg) :
        RustOracleComp unifSpec C)
      return some
        ({ ikA := p.ikA.identity_key.public_key
           ekA := ekA.public_key
           ct := ag.kyber_ciphertext
           idSPK := b.spkB.2
           idPQPK := b.pqpkB.2
           idOPK := b.opkB.map Prod.snd
           ctxt := ctxt },
         { inputs := ip, coins := R, keys := keys, ad := ad, msg := p.msg }, R')

/-- The one-time prekey that Bob uses for an initial message naming `id`: none if the message
names none, his own if it names his, and no admissible choice (`none`) otherwise. In production
Bob looks the named prekey up in his store; the store is not modelled. -/
def selectOPK [DecidableEq IdC] (P : Params Rand Msg C IdC IdK) (p : RecipientParameters)
    (id : Option IdC) : Option (Option ECKeyPair) :=
  match id, p.opkB with
  | none, _ => some none
  | some i, some opk => if P.idEC opk.public_key = i then some (some opk) else none
  | some _, none => none

/-- **Bob's step on an initial message.** He checks the identifiers of his signed and Kyber
prekeys, selects the one-time prekey the message names, runs the responder's entry point, and
decrypts Alice's synthetic ciphertext. Any failed check, returned protocol error or failed
decryption gives `none`; a fault of extracted code is a fault of the run. -/
def accept [DecidableEq IdC] [DecidableEq IdK] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (p : RecipientParameters) (m : FullInitialMessage C IdC IdK) :
    RustOracleComp unifSpec (Option (BobSession Msg)) := do
  if m.idSPK ≠ P.idEC p.spkB.public_key ∨ m.idPQPK ≠ P.idKEM p.pqpkB.public_key then
    return none
  match selectOPK P p m.idOPK with
  | none => return none
  | some opk =>
      let rp : pqxdh.RecipientParameters :=
        { our_identity_key_pair := p.ikB
          our_signed_pre_key_pair := p.spkB
          our_one_time_pre_key_pair := opk
          our_kyber_pre_key_pair := p.pqpkB
          their_identity_key := { public_key := m.ikA }
          their_ephemeral_key := m.ekA
          their_kyber_ciphertext := m.ct
          self_session := false }
      let res ← liftResult (E.accept rp)
      match res with
      | .Err _ => return none
      | .Ok hk =>
          let keys := JointKeys.ofHandshakeKeys hk
          let ad := (m.ikA, p.ikB.identity_key.public_key, p.pqpkB.public_key)
          match P.aead.decrypt (syntheticAeadRoles keys).alice ad m.ctxt with
          | some msg => return some { inputs := rp, keys := keys, ad := ad, msg := msg }
          | none => return none

/-- Alice's check of Bob's confirmation: it decrypts under the synthetic key to her message. -/
def confirmOk [DecidableEq Msg] (P : Params Rand Msg C IdC IdK) (s : AliceSession Rand Msg)
    (conf : C) : Bool :=
  decide (P.aead.decrypt (syntheticAeadRoles s.keys).bob s.ad conf = some s.msg)

/-- Alice's states: waiting for a bundle with her generator state, waiting for the confirmation
after sending her initial message, and completed. -/
inductive InitiatorState (Rand Msg : Type) where
  /-- Waiting for a bundle. -/
  | start (p : InitiatorParameters Msg) (R : Rand)
  /-- Initial message sent; waiting for the confirmation. -/
  | sent (s : AliceSession Rand Msg) (R : Rand)
  /-- Completed. -/
  | done (s : AliceSession Rand Msg)

/-- The joint output of a completed Alice state, and none before completion. -/
def InitiatorState.jointKeys : InitiatorState Rand Msg → Option JointKeys
  | .done s => some s.keys
  | _ => none

/-- Bob's states: unable to publish after a signing error, waiting for an initial message, and
completed. -/
inductive RecipientState (Msg : Type) where
  /-- Signing returned an error; the session does nothing. -/
  | dead
  /-- Bundle published; waiting for the initial message. -/
  | awaiting (p : RecipientParameters)
  /-- Completed. -/
  | done (s : BobSession Msg)

/-- The joint output of a completed Bob state, and none before completion. -/
def RecipientState.jointKeys : RecipientState Msg → Option JointKeys
  | .done s => some s.keys
  | _ => none

/-- Bob's start of a session: unless signing his signed prekey failed, he draws his one-time
and Kyber prekey pairs and publishes his bundle. -/
def recipientInit (P : Params Rand Msg C IdC IdK) (hasOPK : Bool) (idn : RecipientIdentity) :
    RustOracleComp unifSpec (Party.InitResult (RecipientState Msg) (FullMessage C IdC IdK)) :=
  match idn.spkSigB with
  | .Err _ => pure (.waitForMsg .dead)
  | .Ok spkSig => do
      let opkB ← (liftM (genOPK P hasOPK) : RustOracleComp unifSpec (Option ECKeyPair))
      let pqpkB ← (liftM P.pqKeygen : RustOracleComp unifSpec PQKeyPair)
      let p : RecipientParameters :=
        { ikB := idn.ikB, spkB := idn.spkB, spkSigB := spkSig, opkB := opkB, pqpkB := pqpkB }
      match ← publish P p with
      | .Ok bundle => pure (.speakFirst (.awaiting p) (.bundle bundle))
      | .Err _ => pure (.waitForMsg .dead)

/-- Alice in the three-message scheme: she answers a bundle with her initial message and
completes on Bob's confirmation. Her output is the root key. -/
def initiator [DecidableEq Msg] (P : Params Rand Msg C IdC IdK) (E : EntryPoints Rand) :
    Party (RustOracleComp unifSpec) (InitiatorParameters Msg) (FullMessage C IdC IdK)
      (Option Key) where
  State := InitiatorState Rand Msg
  init p := do
    let R ← (liftM P.coins : RustOracleComp unifSpec Rand)
    pure (.waitForMsg (.start p R))
  step st w := match st, w with
    | .start p R, .bundle b => do
        match ← initiate P E p R b with
        | some (im, s, R') => pure (.acceptAndSend (.sent s R') (.initial im) false)
        | none => pure .reject
    | .sent s _, .confirmation conf =>
        if confirmOk P s conf then pure (.complete (.done s)) else pure .reject
    | _, _ => pure .reject
  output st := pure (st.jointKeys.map fun j => some j.root)

/-- Bob in the three-message scheme: he publishes his bundle, answers Alice's initial message with
his confirmation and completes. His output is the root key. -/
def recipient [DecidableEq IdC] [DecidableEq IdK] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (hasOPK : Bool) :
    Party (RustOracleComp unifSpec) RecipientIdentity (FullMessage C IdC IdK) (Option Key) where
  State := RecipientState Msg
  init := recipientInit P hasOPK
  step st w := match st, w with
    | .awaiting p, .initial im => do
        match ← accept P E p im with
        | some s => do
            let conf ← (liftM (P.aead.encrypt (syntheticAeadRoles s.keys).bob s.ad s.msg) :
              RustOracleComp unifSpec C)
            pure (.acceptAndSend (.done s) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output st := pure (st.jointKeys.map fun j => some j.root)

/-- Alice in the two-message scheme: she answers a bundle with her initial message and completes
at once. -/
def initiatorNoConfirm (P : Params Rand Msg C IdC IdK) (E : EntryPoints Rand) :
    Party (RustOracleComp unifSpec) (InitiatorParameters Msg) (FullMessage C IdC IdK)
      (Option Key) where
  State := InitiatorState Rand Msg
  init p := do
    let R ← (liftM P.coins : RustOracleComp unifSpec Rand)
    pure (.waitForMsg (.start p R))
  step st w := match st, w with
    | .start p R, .bundle b => do
        match ← initiate P E p R b with
        | some (im, s, _) => pure (.acceptAndSend (.done s) (.initial im) true)
        | none => pure .reject
    | _, _ => pure .reject
  output st := pure (st.jointKeys.map fun j => some j.root)

/-- Bob in the two-message scheme: he publishes his bundle and completes on Alice's initial
message. -/
def recipientNoConfirm [DecidableEq IdC] [DecidableEq IdK] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (hasOPK : Bool) :
    Party (RustOracleComp unifSpec) RecipientIdentity (FullMessage C IdC IdK) (Option Key) where
  State := RecipientState Msg
  init := recipientInit P hasOPK
  step st w := match st, w with
    | .awaiting p, .initial im => do
        match ← accept P E p im with
        | some s => pure (.complete (.done s))
        | none => pure .reject
    | _, _ => pure .reject
  output st := pure (st.jointKeys.map fun j => some j.root)

/-- **The Full realization with Bob authenticated.** Three messages: Bob's bundle, Alice's
initial message and Bob's confirmation. Alice is the unauthenticated party U and Bob the
authenticated party T. The security statements concern this scheme. -/
def uakeInitiator [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Params Rand Msg C IdC IdK) (E : EntryPoints Rand) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme (RustOracleComp unifSpec) Key (InitiatorParameters Msg) RecipientIdentity
      (FullMessage C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P E
  T := recipient P E hasOPK

/-- **The Full realization with Alice authenticated, for correctness only.** Two messages: Bob's
bundle and Alice's initial message. Bob is the unauthenticated party U and Alice the
authenticated party T. No security statement concerns this scheme: Alice signs nothing, so the
UAKE notion does not fit this direction. -/
def uakeRecipient [DecidableEq IdC] [DecidableEq IdK] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme (RustOracleComp unifSpec) Key RecipientIdentity (InitiatorParameters Msg)
      (FullMessage C IdC IdK) where
  rounds := 2
  setup := Prod.swap <$> setup P msg
  U := recipientNoConfirm P E hasOPK
  T := initiatorNoConfirm P E

/-- **Projection, Alice.** In both schemes Alice's output is the root key of her stored joint
output, and nothing before completion. -/
theorem initiator_output_eq [DecidableEq Msg] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (st : InitiatorState Rand Msg) :
    (initiator P E).output st = pure (st.jointKeys.map fun j => some j.root) ∧
      (initiatorNoConfirm P E).output st = pure (st.jointKeys.map fun j => some j.root) :=
  ⟨rfl, rfl⟩

/-- **Projection, Bob.** In both schemes Bob's output is the root key of his stored joint output,
and nothing before completion. -/
theorem recipient_output_eq [DecidableEq IdC] [DecidableEq IdK] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (hasOPK : Bool) (st : RecipientState Msg) :
    (recipient P E hasOPK).output st = pure (st.jointKeys.map fun j => some j.root) ∧
      (recipientNoConfirm P E hasOPK).output st = pure (st.jointKeys.map fun j => some j.root) :=
  ⟨rfl, rfl⟩

end

end Protocols.PQXDH.Realization
