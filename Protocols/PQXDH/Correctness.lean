/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Contracts
import Protocols.PQXDH.HonestRun
import Protocols.PQXDH.Scheme
import Libsignal.Proofs.Protocol.Crypto.HkdfSha256

/-!
# Correctness of the Full realization

Core completion (`coreCompletion_extracted`) and joint key-record agreement
(`jointKeyAgreement_extracted`) concern an honest PQXDH run on the extracted handshake alone.
Wrapper agreement (`wrapperAgreement_uakeInitiator`, `wrapperAgreement_uakeRecipient`) adds the
synthetic wrapper of `Scheme.lean`.

Each statement bounds from below the probability of success in an honest run, without
conditioning on success. Rejections, protocol errors, panics and divergence count as failures.
Faults contribute only missing probability mass.

The agreement statements hold with probability at least `1 - δ`, where `δ` bounds the
correctness error of the extracted Kyber operations (`KyberDeltaCorrect`). For `δ = 0` they
become probability-one statements. For `δ > 0`, the parties can hold different keys after a Kyber
mismatch, and a party can then reject the other's synthetic ciphertext.

The fixtures in `ProtocolsTest/PQXDH/FaultFixtures.lean` show that the success events
are not vacuous: entry points that always panic, always return an error or never terminate fail
every statement for every `δ < 1`.

The proofs of the two wrapper statements are stubs, which `Protocols/LEDGER.md` lists as temporary
stubs. The two core statements are proved from the honest run of `HonestRun.lean`.
-/

open OracleSpec OracleComp AKE ENNReal
open Aeneas Aeneas.Std
open libsignal_protocol
open Protocols.Realization

namespace Protocols.PQXDH

noncomputable section

variable {Rand Msg C IdC IdK : Type}

/-- The honest core run. Draw Alice's identity and ephemeral key pairs, Bob's identity, signed,
one-time (when `hasOPK`) and Kyber key pairs from the ideal generators, and Alice's generator state
from `P.coins`. Run the initiator's entry point and, if it returns an agreement, the responder's
entry point on Alice's ciphertext. The result is what each entry point returned. The responder's
result is absent when the initiator returned an error. -/
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

/-- Core completion: on honest inputs, the extracted `pqxdh_initiate` and `pqxdh_accept` both
return their keys with probability `1`. The hypotheses are the leaf contracts, the HKDF contract
for some MAC interface `H`, valid curve25519 pairs from `P.ecKeygen`, Kyber1024-shaped pairs from
`P.pqKeygen`, and a generator total on a domain that contains every state drawn from `P.coins`.

Completion does not depend on Kyber's correctness. Kyber decapsulation returns a secret even when
it disagrees with the encapsulated one (`rust/protocol/src/kem/kyber1024.rs:42-54`), and
`pqxdh_accept` derives keys without checking them (`rust/protocol/src/pqxdh.rs:379-386`). -/
theorem coreCompletion_extracted (P : Params Rand Msg C IdC IdK) (hasOPK : Bool)
    (hC : CoreContracts) (H : crypto.HmacSha256) (hH : crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r) :
    rustRuntime.evalDist (coreCompletionExp P EntryPoints.extracted hasOPK) {true} = 1 := by
  rw [rustRuntime_evalDist_true]
  refine le_antisymm (prEvent_le_one _) ?_
  simp only [coreCompletionExp, coreHonestRun, bind_assoc]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun ikA hikA => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun ikB hikB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun spkB hspkB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun opkB hopkB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun pqpkB hpqpkB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun ekA hekA => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun R hR => ?_
  rw [ExceptT.support_liftM] at hikA hikB hspkB hopkB hpqpkB hekA hR
  obtain ⟨ss, ct, ss', r', hkA, hkB, -, -, hinit, hacc, -, -⟩ :=
    honest_run_ok hC H hH P.rngInst P.cryptoRngInst Dom hRng ikA ikB spkB ekA opkB pqpkB R
      (hEC _ hikA) (hEC _ hikB) (hEC _ hspkB) (hEC _ hekA)
      (genOPK_valid P hasOPK hEC _ hopkB) (hPQ _ hpqpkB) (hCoins _ hR)
  simp only [EntryPoints.extracted, hinit, hacc, liftResult_ok, pure_bind]
  rw [prEvent_pure]
  simp

/-- Joint key-record agreement: on honest inputs, both extracted entry points return their keys,
the two joint outputs agree on the root key, the chain key with its index and the post-quantum
ratchet key, and the chain index is `0`, with probability at least `1 - δ`. Here `δ` bounds the
correctness error of the extracted Kyber operations, and a Kyber mismatch is the only way the
keys can differ. The hypotheses are those of `coreCompletion_extracted` and
`KyberDeltaCorrect P δ`. -/
theorem jointKeyAgreement_extracted (P : Params Rand Msg C IdC IdK) (hasOPK : Bool)
    (hC : CoreContracts) (H : crypto.HmacSha256) (hH : crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r) (δ : ℝ≥0∞) (hδ : KyberDeltaCorrect P δ) :
    1 - δ ≤ rustRuntime.evalDist (jointKeyExp P EntryPoints.extracted hasOPK) {true} := by
  refine (KEMScheme.one_sub_le_probOutput_of_deltaCorrect hδ).trans ?_
  rw [rustRuntime_evalDist_true, rustRuntime_evalDist_true]
  simp only [jointKeyExp, coreHonestRun, KEMScheme.correctnessExperiment, kyberKem, bind_assoc,
    pure_bind]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun ikA hikA => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun ikB hikB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun spkB hspkB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun opkB hopkB => ?_
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun pqpkB hpqpkB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _
    fun ekA hekA => ?_
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun R hR => ?_
  rw [ExceptT.support_liftM] at hikA hikB hspkB hopkB hpqpkB hekA hR
  obtain ⟨ss, ct, ss', r', hkA, hkB, henc, hdec, hinit, hacc, hidx, hagree⟩ :=
    honest_run_ok hC H hH P.rngInst P.cryptoRngInst Dom hRng ikA ikB spkB ekA opkB pqpkB R
      (hEC _ hikA) (hEC _ hikB) (hEC _ hspkB) (hEC _ hekA)
      (genOPK_valid P hasOPK hEC _ hopkB) (hPQ _ hpqpkB) (hCoins _ hR)
  simp only [EntryPoints.extracted, henc, hdec, hinit, hacc, liftResult_ok, pure_bind]
  rw [prEvent_pure, prEvent_pure]
  by_cases h : ss' = ss
  · subst h
    have hk := hagree rfl
    subst hk
    simp [JointKeys.ofHandshakeKeys, hidx]
  · simp [h]

/-- Wrapper agreement with Bob authenticated: in an honest run of `uakeInitiator` on the extracted
entry points, both parties output a key and the two keys are equal, with probability at least
`1 - δ`. The hypotheses are those of `jointKeyAgreement_extracted`, the signature contracts,
totality of the generator's `rand::Rng` view on `Dom` (signing uses it), and perfect correctness
of the synthetic AEAD. The proof is a temporary stub. -/
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
    1 - δ ≤ rustRuntime.evalDist
      (UAKE.agreementExp (uakeInitiator P EntryPoints.extracted msg hasOPK)) {true} := by
  sorry

/-- Wrapper agreement with Alice authenticated: in an honest run of `uakeRecipient` on the
extracted entry points, both parties output a key and the two keys are equal, with probability at
least `1 - δ`. The hypotheses are those of `wrapperAgreement_uakeInitiator`. This direction is
correctness-only. The proof is a temporary stub. -/
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
    1 - δ ≤ rustRuntime.evalDist
      (UAKE.agreementExp (uakeRecipient P EntryPoints.extracted msg hasOPK)) {true} := by
  sorry

end

end Protocols.PQXDH
