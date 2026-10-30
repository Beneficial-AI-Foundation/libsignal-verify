/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.PQXDH.Realization.Contracts
import Protocols.PQXDH.Realization.Scheme
import Libsignal.Spec.Protocol.Crypto.HkdfSha256

/-!
# Correctness of the Full realization

Three statements say that PQXDH, run honestly on the extracted entry points, works. Each one is
the probability of a success event in an honest run, and none is conditioned on success: a run in
which a party rejects, an entry point returns a protocol error, or extracted code panics or does
not terminate counts as a failure. A faulted run is missing probability mass, which never counts
towards a success probability.

1. **Core completion** (`coreCompletion_extracted`). On honest inputs drawn from the shared
   generators and generator state, both entry points return their keys, with probability `1`.
   Kyber decapsulation returns a secret even when it disagrees with the encapsulated one
   (`rust/protocol/src/kem/kyber1024.rs:42-54`), and `pqxdh_accept` derives keys without checking
   them (`rust/protocol/src/pqxdh.rs:379-386`), so completion does not depend on the KEM's
   correctness.
2. **Joint key-record agreement** (`jointKeyAgreement_extracted`). Both entry points return their
   keys, the two parties' `JointKeys` are equal (root key, chain key with its index,
   post-quantum ratchet key) and the chain index is `0`, with probability at least `1 - δ`. Here
   `δ` bounds the correctness error of the extracted Kyber operations (`KyberDeltaCorrect`); a
   Kyber mismatch is the only way the keys can differ.
3. **Wrapper agreement** (`wrapperAgreement_uakeInitiator`, `wrapperAgreement_uakeRecipient`).
   In an honest run of the Full UAKE scheme both parties output a key and the two keys are equal,
   with probability at least `1 - δ`. This adds the synthetic wrapper: signatures, identity
   checks and the AEAD messages.

The first two statements concern the core realization and do not involve the AEAD gate. All
three take, as named hypotheses, the contracts of the opaque leaves (`CoreContracts`,
`SignatureContracts`), the HKDF contract, the policies on the ideal generators (valid
curve25519 pairs, Kyber1024-shaped Kyber pairs), and the RNG-totality hypothesis together with
the domain `Dom` of the generator states drawn from `P.coins`. None assumes perfect Kyber
correctness. For `δ = 0` the second and third statements become probability-one statements; for
`δ > 0` honest completion of the wrapper is not expected: after a Kyber mismatch the parties hold
different keys, and a party may reject the other's synthetic ciphertext.

The fixtures in `ProtocolsTest/PQXDH/Realization/FaultFixtures.lean` check that the success
events are not vacuous: entry points that always panic, always return an error or never
terminate give each event probability `0`, so they fail every statement for every `δ < 1`.

The proofs of the four theorems are stubs, to be completed in M1.
-/

open OracleSpec OracleComp AKE ENNReal
open Aeneas Aeneas.Std
open libsignal_protocol
open Protocols.Realization

namespace Protocols.PQXDH.Realization

noncomputable section

variable {Rand Msg C IdC IdK : Type}

/-- **The honest core run.** Draw Alice's identity and ephemeral key pairs, Bob's identity, signed,
one-time (when `hasOPK`) and Kyber key pairs from the ideal generators, and Alice's generator state
from `P.coins`; run the initiator's entry point and, if it returns an agreement, the responder's
entry point on Alice's ciphertext. The result is what each entry point returned; the responder's is
absent when the initiator returned an error. -/
def coreHonestRun (P : Params Rand Msg C IdC IdK) (E : EntryPoints Rand) (hasOPK : Bool) :
    RustOracleComp unifSpec
      (core.result.Result InitiatorAgreement error.SignalProtocolError ×
        Option (core.result.Result HandshakeKeys error.SignalProtocolError)) := do
  let ikA ← (liftM P.ecKeygen : RustOracleComp unifSpec ECKeyPair)
  let ikB ← (liftM P.ecKeygen : RustOracleComp unifSpec ECKeyPair)
  let spkB ← (liftM P.ecKeygen : RustOracleComp unifSpec ECKeyPair)
  let opkB ← (liftM (genOPK P hasOPK) : RustOracleComp unifSpec (Option ECKeyPair))
  let pqpkB ← (liftM P.pqKeygen : RustOracleComp unifSpec PQKeyPair)
  let ekA ← (liftM P.ecKeygen : RustOracleComp unifSpec ECKeyPair)
  let R ← (liftM P.coins : RustOracleComp unifSpec Rand)
  let ip : pqxdh.InitiatorParameters :=
    { our_identity_key_pair := identityKeyPairOf ikA
      our_ephemeral_key_pair := ekA
      their_identity_key := identityKeyOf ikB
      their_signed_pre_key := spkB.public_key
      their_one_time_pre_key := opkB.map (·.public_key)
      their_ratchet_key := spkB.public_key
      their_kyber_pre_key := pqpkB.public_key
      self_session := false }
  let (resA, _) ← liftResult (E.initiate P.rngInst P.cryptoRngInst ip R)
  match resA with
  | .Err e => pure (.Err e, none)
  | .Ok ag =>
      let rp : pqxdh.RecipientParameters :=
        { our_identity_key_pair := identityKeyPairOf ikB
          our_signed_pre_key_pair := spkB
          our_one_time_pre_key_pair := opkB
          our_kyber_pre_key_pair := pqpkB
          their_identity_key := identityKeyOf ikA
          their_ephemeral_key := ekA.public_key
          their_kyber_ciphertext := ag.kyber_ciphertext
          self_session := false }
      let resB ← liftResult (E.accept rp)
      pure (.Ok ag, some resB)

/-- The core-completion event: both entry points returned their keys. -/
def coreCompletionExp (P : Params Rand Msg C IdC IdK) (E : EntryPoints Rand) (hasOPK : Bool) :
    RustOracleComp unifSpec Bool := do
  let (resA, resB) ← coreHonestRun P E hasOPK
  pure (match resA, resB with
    | .Ok _, some (.Ok _) => true
    | _, _ => false)

/-- The joint key-record event: both entry points returned their keys, the two joint outputs are
equal, and the chain index is `0`. -/
def jointKeyExp (P : Params Rand Msg C IdC IdK) (E : EntryPoints Rand) (hasOPK : Bool) :
    RustOracleComp unifSpec Bool := do
  let (resA, resB) ← coreHonestRun P E hasOPK
  pure (match resA, resB with
    | .Ok ag, some (.Ok hk) =>
        decide (JointKeys.ofHandshakeKeys ag.keys = JointKeys.ofHandshakeKeys hk ∧
          (JointKeys.ofHandshakeKeys hk).chainIndex = 0#u32)
    | _, _ => false)

open Classical in
/-- The wrapper-agreement event of a UAKE scheme: in an honest run from setup, both parties output
a key and the keys are equal. Unlike `AKE.UAKE.CorrectExp`, a run in which a party outputs no key
counts as a failure. -/
def agreementExp {m : Type → Type} [Monad m] {K UK TK W : Type} (proto : UAKE.Scheme m K UK TK W) :
    m Bool := do
  let (uk, tk) ← proto.setup
  let (uOut, tOut, _) ← proto.U.runHonest proto.T uk tk (proto.rounds + 1)
  pure (decide (uOut.join.isSome ∧ uOut.join = tOut.join))

/-- **Core completion, probability one.** On honest inputs, the extracted `pqxdh_initiate` and
`pqxdh_accept` both return their keys with probability `1`. Hypotheses: the leaf contracts, the
HKDF contract for some MAC interface `H`, valid curve25519 pairs from `P.ecKeygen`,
Kyber1024-shaped pairs from `P.pqKeygen`, and a generator total on a domain that contains every
state drawn from `P.coins`. Stub: the proof is a temporary M1 obligation. -/
theorem coreCompletion_extracted (P : Params Rand Msg C IdC IdK) (hasOPK : Bool)
    (hC : CoreContracts) (H : crypto.HmacSha256) (hH : crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r) :
    Pr[= true | rustRuntime.evalDist (coreCompletionExp P EntryPoints.extracted hasOPK)] = 1 := by
  sorry

/-- **Joint key-record agreement, probability at least `1 - δ`.** On honest inputs, both extracted
entry points return their keys, the two joint outputs agree on the root key, the chain key with
its index and the post-quantum ratchet key, and the chain index is `0`, with probability at least
`1 - δ`, where `δ` bounds the correctness error of the extracted Kyber operations. Hypotheses: as
for `coreCompletion_extracted`, and `KyberDeltaCorrect P δ`. Stub: the proof is a temporary M1
obligation. -/
theorem jointKeyAgreement_extracted (P : Params Rand Msg C IdC IdK) (hasOPK : Bool)
    (hC : CoreContracts) (H : crypto.HmacSha256) (hH : crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r) (δ : ℝ≥0∞) (hδ : KyberDeltaCorrect P δ) :
    1 - δ ≤ Pr[= true | rustRuntime.evalDist (jointKeyExp P EntryPoints.extracted hasOPK)] := by
  sorry

/-- **Wrapper agreement, Bob authenticated, probability at least `1 - δ`.** In an honest run of
`uakeInitiator` on the extracted entry points, both parties output a key and the two keys are
equal, with probability at least `1 - δ`. Hypotheses: as for `jointKeyAgreement_extracted`, the
signature contracts, totality of the generator's `rand::Rng` view on `Dom` (signing uses it), and
perfect correctness of the synthetic AEAD. Stub: the proof is a temporary M1 obligation. -/
theorem wrapperAgreement_uakeInitiator [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hC : CoreContracts) (hS : SignatureContracts)
    (H : crypto.HmacSha256) (hH : crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r) (hAead : AEAD.PerfectlyCorrect P.aead)
    (δ : ℝ≥0∞) (hδ : KyberDeltaCorrect P δ) :
    1 - δ ≤ Pr[= true | rustRuntime.evalDist
      (agreementExp (uakeInitiator P EntryPoints.extracted msg hasOPK))] := by
  sorry

/-- **Wrapper agreement, Alice authenticated, probability at least `1 - δ`.** In an honest run of
`uakeRecipient` on the extracted entry points, both parties output a key and the two keys are
equal, with probability at least `1 - δ`. Hypotheses: as for `wrapperAgreement_uakeInitiator`.
This direction is correctness-only. Stub: the proof is a temporary M1 obligation. -/
theorem wrapperAgreement_uakeRecipient [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hC : CoreContracts) (hS : SignatureContracts)
    (H : crypto.HmacSha256) (hH : crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r) (hAead : AEAD.PerfectlyCorrect P.aead)
    (δ : ℝ≥0∞) (hδ : KyberDeltaCorrect P δ) :
    1 - δ ≤ Pr[= true | rustRuntime.evalDist
      (agreementExp (uakeRecipient P EntryPoints.extracted msg hasOPK))] := by
  sorry

end

end Protocols.PQXDH.Realization
