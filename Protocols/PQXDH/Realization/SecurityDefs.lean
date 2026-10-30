/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.PQXDH.Realization.Contracts
import Protocols.PQXDH.Realization.Witness
import VCVio.CryptoFoundations.PRF

/-!
# Premises of the security statements of the Full realization

The security statements of the Full realization bound an adversary's advantage by the advantages
of adversaries against the primitives. This file defines those primitive games, stated on the
extracted code or on the interfaces that its contracts name, and the remaining premises.

* **Signatures** (`jointSigAdvantage`). Bob's single identity key both signs and performs
  Diffie-Hellman. The game is existential unforgeability under chosen messages *with an agreement
  oracle on the same key*: the adversary gets the identity public key, a signing oracle that runs
  the extracted signing through the fault-preserving adapter `signBytes`, and an oracle that
  returns the extracted agreement of the identity private key with any public key it chooses. It
  wins with a signature that verifies, by the extracted verification, on a message it never asked
  to be signed. Strong unforgeability is not used: production verification accepts `(R, s + ℓ)`
  whenever it accepts `(R, s)` (`rust/core/src/curve/curve25519.rs:134-155`), so it is false. The
  game is defined here because VCVio's unforgeability games are typed over `OracleComp` only. It
  scores a winning probability, so a fault only lowers it.
* **Diffie-Hellman** (`fullGapDHAdvantage`). Gap computational Diffie-Hellman for the extracted
  X25519 and the Full key generator: given two public keys from `P.ecKeygen`, compute their
  agreement, with an oracle that decides whether `Z` is the agreement of some private key of `X`
  with `Y`. No uniform-exponent law is involved: the keys are those of the Full generator.
* **Key derivation** (`kdfPRFDH`, `kdfPRF`). The key derivation is the RFC 5869 HKDF of the MAC
  interface `H` that `HkdfSha256Contract H` names, on the PQXDH input layout and label. As in
  PQXDH-model, it is assumed to be a pseudorandom function keyed by the third Diffie-Hellman value
  (a public key from `P.ecKeygen` in that slot, for the DH statement) or by the Kyber secret (a
  uniform 32-byte key, for the PQ statement).
* **Kyber** (`KyberBridge`). The PQ statement assumes IND-CCA security of an abstract total KEM
  `K`, VCVio's notion, as the model's PQ theorem does. The bridge contract ties `K` to the
  extracted calls: `P.pqKeygen` is `K`'s key generation, `K`'s encapsulation is a function of the
  generator state drawn from `P.coins`, and every extracted encapsulation on a 1568-byte key and
  every extracted decapsulation with an honest secret key either faults or returns `K`'s output.
  It claims no termination; faulted runs are counted separately. Production runs libcrux's
  pre-standard Kyber-1024, not ML-KEM-1024. Out of scope here: the correctness of libcrux's Kyber
  against the Kyber specification, the IND-CCA security of Kyber itself (a hardness assumption),
  and ML-KEM Braid.
* **Fitting messages** (`Adversary.SendsFittingMessages`). The extraction's byte slices may be as
  long as the largest `usize`, which no Rust allocation reaches. A bundle carrying a Kyber key of
  that length makes the serialization in Alice's signature check overflow, a fault that cannot
  occur in production. The statement that the experiment loses no mass assumes that the adversary
  never sends such a key; the security bounds themselves do not.
-/

open OracleSpec OracleComp AKE AKE.UAKE ENNReal
open Aeneas Aeneas.Std
open libsignal_protocol
open Protocols.Realization

namespace Protocols.PQXDH.Realization

noncomputable section

variable {Rand Msg C IdC IdK : Type}

section Signature

/-- The result of an extracted signing call or agreement call. -/
abbrev CurveResult : Type := core.result.Result (Slice U8) libsignal_core.curve.CurveError

/-- The oracles of the joint unforgeability game: uniform sampling, signing of a byte string and
agreement with a public key. -/
abbrev JointSigOracleSpec :=
  unifSpec + ((Slice U8 →ₒ CurveResult) + (ECPub →ₒ CurveResult))

/-- An adversary against joint unforgeability: from the identity public key, with the oracles of
`JointSigOracleSpec`, it outputs a message and a signature. -/
structure JointSigAdversary where
  /-- The adversary's computation. -/
  main : ECPub → OracleComp JointSigOracleSpec (Slice U8 × Slice U8)

/-- The oracles of the joint unforgeability game for the identity private key `sk`: signing runs
the fault-preserving adapter and records the message; agreement runs the extracted agreement. -/
def jointSigImpl (P : Params Rand Msg C IdC IdK) (sk : ECPriv) :
    QueryImpl JointSigOracleSpec (StateT (List (Slice U8)) (RustOracleComp unifSpec)) :=
  let unifImpl : QueryImpl unifSpec (StateT (List (Slice U8)) (RustOracleComp unifSpec)) :=
    fun t => liftM (liftM ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) t) :
      RustOracleComp unifSpec _)
  let signImpl : QueryImpl (Slice U8 →ₒ CurveResult)
      (StateT (List (Slice U8)) (RustOracleComp unifSpec)) := fun msg => do
    modify (msg :: ·)
    liftM (signBytes P sk msg)
  let agreeImpl : QueryImpl (ECPub →ₒ CurveResult)
      (StateT (List (Slice U8)) (RustOracleComp unifSpec)) := fun pk =>
    liftM (liftResult (curve.PrivateKey.calculate_agreement sk pk) : RustOracleComp unifSpec _)
  unifImpl + (signImpl + agreeImpl)

/-- **The joint unforgeability game.** Draw the identity key pair from `P.ecKeygen`, run the
adversary with the signing and agreement oracles, and verify its output with the extracted
verification. The adversary wins when the signature verifies and the message was never signed. -/
def jointSigForgeExp (P : Params Rand Msg C IdC IdK) (A : JointSigAdversary) :
    RustOracleComp unifSpec Bool := do
  let kp ← (liftM P.ecKeygen : RustOracleComp unifSpec ECKeyPair)
  let ((msg, σ), signed) ← (simulateQ (jointSigImpl P kp.private_key) (A.main kp.public_key)).run []
  let ok ← verifyBytes kp.public_key msg σ
  pure (ok && decide (msg ∉ signed))

/-- The adversary's success probability in the joint unforgeability game. -/
def jointSigAdvantage (P : Params Rand Msg C IdC IdK) (A : JointSigAdversary) : ℝ≥0∞ :=
  Pr[= true | rustRuntime.evalDist (jointSigForgeExp P A)]

end Signature

section DiffieHellman

/-- `Z` is the agreement of some private key whose public half is `X` with the public key `Y`. -/
def IsAgreement (X Y : ECPub) (Z : Slice U8) : Prop :=
  ∃ x : ECPriv, curve.PrivateKey.public_key x = .ok (.Ok X) ∧
    curve.PrivateKey.calculate_agreement x Y = .ok (.Ok Z)

/-- The oracles of the gap Diffie-Hellman game: uniform sampling and a decision oracle for
`IsAgreement`. -/
abbrev FullDDHOracleSpec := unifSpec + ((ECPub × ECPub × Slice U8) →ₒ Bool)

/-- An adversary against gap Diffie-Hellman: from two public keys, with the decision oracle, it
outputs a candidate agreement. -/
def FullGapDHAdversary : Type := ECPub → ECPub → OracleComp FullDDHOracleSpec (Slice U8)

open Classical in
/-- The oracles of the gap Diffie-Hellman game. -/
def fullDDHImpl : QueryImpl FullDDHOracleSpec ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    fun q : ECPub × ECPub × Slice U8 =>
      (pure (decide (IsAgreement q.1 q.2.1 q.2.2)) : ProbComp Bool)

open Classical in
/-- **Gap Diffie-Hellman for the extracted X25519.** Draw two key pairs from `P.ecKeygen`; the
adversary wins when it outputs their agreement. -/
def fullGapDHExp (P : Params Rand Msg C IdC IdK) (A : FullGapDHAdversary) : ProbComp Bool := do
  let a ← P.ecKeygen
  let b ← P.ecKeygen
  let z ← simulateQ fullDDHImpl (A a.public_key b.public_key)
  pure (decide (curve.PrivateKey.calculate_agreement a.private_key b.public_key = .ok (.Ok z)))

/-- The adversary's success probability in the gap Diffie-Hellman game. -/
def fullGapDHAdvantage (P : Params Rand Msg C IdC IdK) (A : FullGapDHAdversary) : ℝ :=
  (Pr[= true | fullGapDHExp P A]).toReal

end DiffieHellman

section Kdf

/-- The label of the PQXDH key derivation, `WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024`
(`rust/protocol/src/pqxdh.rs:72-77`). -/
def kdfLabel : List U8 :=
  [87#u8, 104#u8, 105#u8, 115#u8, 112#u8, 101#u8, 114#u8, 84#u8, 101#u8, 120#u8, 116#u8, 95#u8,
    88#u8, 50#u8, 53#u8, 53#u8, 49#u8, 57#u8, 95#u8, 83#u8, 72#u8, 65#u8, 45#u8, 50#u8, 53#u8,
    54#u8, 95#u8, 67#u8, 82#u8, 89#u8, 83#u8, 84#u8, 65#u8, 76#u8, 83#u8, 45#u8, 75#u8, 89#u8,
    66#u8, 69#u8, 82#u8, 45#u8, 49#u8, 48#u8, 50#u8, 52#u8]

/-- The PQXDH key-derivation input: 32 bytes of `0xFF`, the three or four Diffie-Hellman values
and the Kyber secret. -/
def kdfInputBytes (d1 d2 d3 : Key) (d4 : Option Key) (ss : Key) : List U8 :=
  List.replicate 32 255#u8 ++ d1.val ++ d2.val ++ d3.val ++
    (match d4 with | some d => d.val | none => []) ++ ss.val

/-- The three 32-byte keys of the RFC 5869 output of `H` on the PQXDH input layout and label: the
root key, the chain key and the post-quantum ratchet key, as `HandshakeKeys::derive` cuts them. -/
def kdfSpec (H : crypto.HmacSha256) (d1 d2 d3 : Key) (d4 : Option Key) (ss : Key) :
    Key × Key × Key :=
  let okm := crypto.hkdfSha256Okm96 H none (kdfInputBytes d1 d2 d3 d4 ss) kdfLabel
  have h : okm.length = 96 := crypto.hkdfExpand96_length _ _ _
  (Aeneas.Std.Array.from (okm.take 32) (by simp [h]),
    Aeneas.Std.Array.from ((okm.drop 32).take 32) (by simp [h]),
    Aeneas.Std.Array.from (okm.drop 64) (by simp [h]))

/-- The key derivation as a pseudorandom function keyed by the third Diffie-Hellman value, for the
DH statement: the key is a public key drawn from `P.ecKeygen`, which stands for a fresh
Diffie-Hellman output, and the input is the rest of the key material. -/
def kdfPRFDH (H : crypto.HmacSha256) (P : Params Rand Msg C IdC IdK) :
    PRFScheme ECKeyPair (Key × Key × Option Key × Key) (Key × Key × Key) where
  keygen := P.ecKeygen
  eval kp q := kdfSpec H q.1 q.2.1 (pubBytes kp.public_key) q.2.2.1 q.2.2.2

/-- The key derivation as a pseudorandom function keyed by the Kyber secret, for the PQ
statement: the key is a uniform 32-byte secret and the input is the Diffie-Hellman values. -/
def kdfPRF (H : crypto.HmacSha256) : PRFScheme Key (Key × Key × Key × Option Key) (Key × Key × Key)
    where
  keygen := $ᵗ Key
  eval ss q := kdfSpec H q.1 q.2.1 q.2.2.1 q.2.2.2 ss

end Kdf

section Kyber

/-- **Bridge contract for Kyber.** The abstract KEM `K` describes the extracted Kyber operations:
`P.pqKeygen` is `K`'s key generation; `K`'s encapsulation is a function `encDet` of the public key
and of the generator state drawn from `P.coins`, and its decapsulation is a function `decDet`; and
every extracted encapsulation on a 1568-byte key, and every extracted decapsulation with a secret
key from `P.pqKeygen`, either faults or returns what `encDet` or `decDet` gives, a returned error
standing for no key. The bridge claims no termination. The branches on keys of other lengths are
the subject of `KyberPartial`. -/
def KyberBridge (P : Params Rand Msg C IdC IdK)
    (K : KEMScheme ProbComp Key PQPub PQPriv (Slice U8)) : Prop :=
  P.pqKeygen = (fun x => ({ public_key := x.1, secret_key := x.2 } : PQKeyPair)) <$> K.keygen ∧
  ∃ (encDet : PQPub → Rand → Slice U8 × Key) (decDet : PQPriv → Slice U8 → Option Key),
    (∀ pk, K.encaps pk = encDet pk <$> P.coins) ∧
    (∀ sk ct, K.decaps sk ct = pure (decDet sk ct)) ∧
    (∀ (pk : PQPub) (r r' : Rand) res, pk.key_data.data.length = 1568 →
      kem.KeyPublic.encapsulate P.cryptoRngInst pk r = .ok (res, r') →
        res = .Ok ((encDet pk r).2.to_slice, (encDet pk r).1)) ∧
    (∀ kp ∈ support P.pqKeygen, ∀ (ct : Slice U8) res,
      kem.KeySecret.decapsulate kp.secret_key ct = .ok res →
        match decDet kp.secret_key ct with
        | some k => res = .Ok k.to_slice
        | none => ∃ e, res = .Err e)

end Kyber

section Fitting

/-- A message fits in memory unless it is a bundle whose Kyber key has the largest `usize`
length, which no Rust allocation reaches. -/
def FitsInMemory : FullMessage C IdC IdK → Prop
  | .bundle b => b.pqpkB.1.key_data.data.length < Usize.max
  | _ => True

open Classical in
/-- The adversary sends only messages that fit in memory, in both of its stages. -/
def Adversary.SendsFittingMessages {K UK TK : Type}
    {proto : UAKE.Scheme (RustOracleComp unifSpec) K UK TK (FullMessage C IdC IdK)}
    (A : UAKE.Adversary proto) : Prop :=
  let bad : ℕ ⊕ Op (FullMessage C IdC IdK) → Prop := fun i =>
    match i with
    | .inr (.stepT _ w) => ¬ FitsInMemory w
    | .inr (.stepChallenge w) => ¬ FitsInMemory w
    | _ => False
  (∀ uk w, (A.challenge uk w).IsQueryBoundP bad 0) ∧ (∀ st k, (A.post st k).IsQueryBoundP bad 0)

end Fitting

end

end Protocols.PQXDH.Realization
