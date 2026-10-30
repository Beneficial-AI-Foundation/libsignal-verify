/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.PQXDH.Realization.Params
import Protocols.Realization.RustOracleComp
import Protocols.ToVCVio.CryptoFoundations.KEMCorrectness

/-!
# The KEM correctness experiment on the extracted Kyber operations

Kyber is not perfectly correct: decapsulating an honestly encapsulated ciphertext returns a
different shared secret with a small probability, about `2^-174` for Kyber1024. The correctness
statements of the Full realization therefore hold with probability at least `1 - δ`, where `δ`
bounds this failure for the extracted Kyber operations. This file defines that bound.

`kyberKem P` packages the extracted `kem::Key<Public>::encapsulate` and
`kem::Key<Secret>::decapsulate` as a VCVio `KEMScheme` in `RustOracleComp unifSpec`. It shares
with the Full scheme the key generator `P.pqKeygen`, the law `P.coins` of the generator state
and the runtime `rustRuntime`. The KEM uses no default value. A protocol error is a value: the
shared secret and the ciphertext are the `Result`s that the extracted calls return, and
decapsulating an encapsulation error returns no key. Hence the experiment
`KEMScheme.CorrectExp` returns `true` only when encapsulation returned a ciphertext and a secret
and decapsulation of that ciphertext returned the same secret (`kyberKem_correctExp_sound`). A
fault in either call is missing mass, which `KEMScheme.correctnessError` counts as error.

`KyberDeltaCorrect P δ` states that this experiment has correctness error at most `δ`. It is a
named hypothesis of the correctness statements, not a fact proved here, and `δ` stays symbolic.
Production calls libcrux's pre-standard Kyber-1024 (`libcrux_ml_kem::kyber1024`,
`rust/protocol/src/kem/kyber1024.rs:6-7`), not ML-KEM-1024. Discharging the hypothesis needs a
model of that backend, a correspondence between the model and the source, and the published
correctness analysis of Kyber. A model of ML-KEM would need its own relation to the pre-standard
variant.
-/

open OracleSpec OracleComp ENNReal
open Aeneas Aeneas.Std
open libsignal_protocol
open Protocols.Realization

namespace Protocols.PQXDH.Realization

/-- A shared secret as the extracted calls return it: the secret bytes, or a protocol error. -/
abbrev KemSecret : Type := core.result.Result (Slice U8) error.SignalProtocolError

/-- A ciphertext as the extracted encapsulation returns it: the serialized ciphertext, or a
protocol error. -/
abbrev KemCiphertext : Type := core.result.Result (Slice U8) error.SignalProtocolError

noncomputable instance : DecidableEq KemSecret := Classical.decEq _

variable {Rand Msg C IdC IdK : Type}

/-- The extracted Kyber operations as a KEM in `RustOracleComp unifSpec`. Key generation is the
ideal generator `P.pqKeygen`. Encapsulation draws the generator state from `P.coins` and runs the
extracted `encapsulate`. Decapsulation runs the extracted `decapsulate`, and it returns no key on
a ciphertext that is itself an error. -/
noncomputable def kyberKem (P : Params Rand Msg C IdC IdK) :
    KEMScheme (RustOracleComp unifSpec) KemSecret PQPub PQPriv KemCiphertext where
  keygen := do
    let kp ← (liftM P.pqKeygen : RustOracleComp unifSpec PQKeyPair)
    pure (kp.public_key, kp.secret_key)
  encaps pk := do
    let r ← (liftM P.coins : RustOracleComp unifSpec Rand)
    let (res, _) ← liftResult (kem.KeyPublic.encapsulate P.cryptoRngInst pk r)
    match res with
    | .Ok (ss, ct) => pure (.Ok ct, .Ok ss)
    | .Err e => pure (.Err e, .Err e)
  decaps sk c :=
    match c with
    | .Ok ct => do
        let res ← liftResult (kem.KeySecret.decapsulate sk ct)
        pure (some res)
    | .Err _ => pure none

/-- If the correctness experiment of `kyberKem P` can return `true`, then some key pair from
`P.pqKeygen` and some state from `P.coins` make the extracted encapsulation return a secret `ss`
and a ciphertext `ct`, and the extracted decapsulation of `ct` return the same `ss`. In
particular, the experiment never counts a protocol error or a fault as a correct run. -/
theorem kyberKem_correctExp_sound (P : Params Rand Msg C IdC IdK)
    (h : true ∈ support (kyberKem P).CorrectExp) :
    ∃ kp ∈ support P.pqKeygen, ∃ r ∈ support P.coins, ∃ (ss ct : Slice U8) (r' : Rand),
      kem.KeyPublic.encapsulate P.cryptoRngInst kp.public_key r = .ok (.Ok (ss, ct), r') ∧
        kem.KeySecret.decapsulate kp.secret_key ct = .ok (.Ok ss) := by
  simp only [KEMScheme.CorrectExp, kyberKem, bind_pure_comp, bind_assoc, bind_map_left,
    support_bind, ExceptT.support_liftM, ExceptT.mem_support_iff, support_map, Set.mem_iUnion,
    Set.mem_image, decide_eq_true_eq, exists_eq_right, exists_prop, Prod.exists,
    exists_and_right] at h
  obtain ⟨kp, hkp, r, hr, a, ⟨r', henc⟩, a₁, b, hmid, hdec⟩ := h
  rw [← ExceptT.mem_support_iff, mem_support_liftResult] at henc
  rcases a with ⟨ss, ct⟩ | e
  · simp only [← ExceptT.mem_support_iff] at hmid
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmid
    obtain ⟨rfl, rfl⟩ := hmid
    simp only [← ExceptT.mem_support_iff] at hdec
    simp only [support_map, Set.mem_image, mem_support_liftResult, Option.some.injEq,
      exists_eq_right] at hdec
    exact ⟨kp, hkp, r, hr, ss, ct, r', henc, hdec⟩
  · simp only [← ExceptT.mem_support_iff] at hmid hdec
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmid
    obtain ⟨rfl, rfl⟩ := hmid
    simp at hdec

/-- `δ`-correctness of the extracted Kyber operations: the correctness error of `kyberKem P`
under `rustRuntime` is at most `δ`. That is, the probability that a key pair from `P.pqKeygen`,
an encapsulation on a state from `P.coins` and the decapsulation of its ciphertext fail to
produce the same secret, counting faults and protocol errors as failures, is at most `δ`. -/
def KyberDeltaCorrect (P : Params Rand Msg C IdC IdK) (δ : ℝ≥0∞) : Prop :=
  (kyberKem P).deltaCorrect rustRuntime δ

end Protocols.PQXDH.Realization
