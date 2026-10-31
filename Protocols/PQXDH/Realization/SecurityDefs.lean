/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Realization.Contracts
import Protocols.PQXDH.Realization.Witness
import VCVio.CryptoFoundations.PRF

/-!
# Premises of the security statements of the Full realization

The security statements of the Full realization bound an adversary's advantage by the advantages
of adversaries against the primitives. This file defines those primitive games, stated on the
extracted code or on the interfaces that its contracts name, and the remaining premises.

* Signatures (`jointSigAdvantage`). Bob's single identity key both signs and performs
  Diffie-Hellman. The game is existential unforgeability under chosen messages *with an agreement
  oracle on the same key*. The adversary gets the identity public key, a signing oracle that runs
  the extracted signing through the fault-preserving adapter `signBytes`, and an oracle that
  returns the extracted agreement of the identity private key with any public key it chooses. It
  wins with a signature that the extracted verification accepts on a message it never asked to be
  signed. Strong unforgeability is false of production, because production verification accepts
  `(R, s + ℓ)` whenever it accepts `(R, s)` (`rust/core/src/curve/curve25519.rs:134-155`). This
  file defines the game because VCVio's unforgeability games are typed over `OracleComp` only. It
  scores a winning probability, so a fault only lowers it.
* Diffie-Hellman and key derivation for the DH statement (`pqxdhODHAdvantage`). One premise of
  the oracle Diffie-Hellman kind covers both. It speaks about the protocol's own Diffie-Hellman
  values and its own key derivation, the RFC 5869 HKDF of the MAC interface `H` that
  `HkdfSha256Contract H` names, on the PQXDH input layout and label.
  - Two key pairs `a` and `b` come from `P.ecKeygen`, and the adversary sees both public keys.
  - It must tell the derived keys of a challenge input, whose third slot is `agree(a, B)` and whose
    fourth slot is `agree(a, Y4)`, from random keys.
  - Meanwhile it can ask for the derived keys of any input whose slots are literals or agreements
    of `a` or `b` with points of its choice.
  - The slot structure is what a reduction needs. Bob's long-term signed prekey enters every one of
    his sessions twice (DH1 and DH3) against points the adversary chooses. Alice's ephemeral key
    meets an unsigned one-time prekey in DH4.
  - The game does not use the uniform-exponent law of the abstract model. Its keys come from the
    Full generator.
* Key derivation for the PQ statement (`kdfPRF`). The key derivation is a pseudorandom function
  keyed by the Kyber secret, a uniform 32-byte key.
* Kyber (`KyberBridge`). The PQ statement assumes IND-CCA security of an abstract total KEM `K`,
  VCVio's notion, as the model's PQ theorem does. The bridge contract ties `K` to the extracted
  calls: `P.pqKeygen` is `K`'s key generation, `K`'s encapsulation is a function of the generator
  state drawn from `P.coins`, and every extracted encapsulation on a 1568-byte key and every
  extracted decapsulation with an honest secret key either faults or returns `K`'s output. It
  claims no termination, and the statements count faulted runs separately. Production runs
  libcrux's pre-standard Kyber-1024, not ML-KEM-1024. Three items are out of scope here:
  - the correctness of libcrux's Kyber against the Kyber specification, which belongs to libcrux
    and Cryspen;
  - the IND-CCA security of Kyber itself, a hardness assumption;
  - ML-KEM Braid, which belongs to SPQR-verify. Its model in secure-messaging PR #397 is passive
    and IND-CPA on ML-KEM, so it does not plug in here.
* Fitting messages (`Adversary.SendsFittingMessages`). The extraction's byte slices can be as long
  as the largest `usize`, which no Rust allocation reaches. A bundle carrying a Kyber key of that
  length makes the serialization in Alice's signature check overflow, a fault that cannot occur in
  production. The statement that the experiment loses no mass assumes that the adversary never
  sends such a key. The security bounds themselves do not assume it.
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

/-- The oracles of the joint unforgeability game for the identity private key `sk`. Signing runs
the fault-preserving adapter and records the message. Agreement runs the extracted agreement. -/
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

/-- The joint unforgeability game. Draw the identity key pair from `P.ecKeygen`, run the
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

/-- The three 32-byte keys of the RFC 5869 output of `H` on the key-derivation input `ikm` and the
PQXDH label: the root key, the chain key and the post-quantum ratchet key, as
`HandshakeKeys::derive` cuts them. -/
def kdfOfBytes (H : crypto.HmacSha256) (ikm : List U8) : Key × Key × Key :=
  let okm := crypto.hkdfSha256Okm96 H none ikm kdfLabel
  have h : okm.length = 96 := crypto.hkdfExpand96_length _ _ _
  (Aeneas.Std.Array.from (okm.take 32) (by simp [h]),
    Aeneas.Std.Array.from ((okm.drop 32).take 32) (by simp [h]),
    Aeneas.Std.Array.from (okm.drop 64) (by simp [h]))

/-- The key derivation on the PQXDH input layout. -/
def kdfSpec (H : crypto.HmacSha256) (d1 d2 d3 : Key) (d4 : Option Key) (ss : Key) :
    Key × Key × Key :=
  kdfOfBytes H (kdfInputBytes d1 d2 d3 d4 ss)

/-- The key derivation as a pseudorandom function keyed by the Kyber secret, for the PQ
statement: the key is a uniform 32-byte secret and the input is the Diffie-Hellman values. -/
def kdfPRF (H : crypto.HmacSha256) : PRFScheme Key (Key × Key × Key × Option Key) (Key × Key × Key)
    where
  keygen := $ᵗ Key
  eval ss q := kdfSpec H q.1 q.2.1 q.2.2.1 q.2.2.2 ss

end Kdf

section ODH

/-- A slot of a key-derivation input in the PQXDH oracle Diffie-Hellman game: a literal 32-byte
value, or the agreement of one of the two embedded private keys `a` and `b` with a public key
that the adversary supplies. -/
inductive DHSlot where
  /-- A literal value. -/
  | lit (v : Key)
  /-- The agreement of `a` with `Y`. -/
  | agreeA (Y : ECPub)
  /-- The agreement of `b` with `Y`. -/
  | agreeB (Y : ECPub)

/-- A key-derivation input with agreement slots: DH1 to DH3, an optional DH4 and the Kyber
secret. -/
structure KdfTemplate where
  /-- The first Diffie-Hellman slot. -/
  dh1 : DHSlot
  /-- The second Diffie-Hellman slot. -/
  dh2 : DHSlot
  /-- The third Diffie-Hellman slot. -/
  dh3 : DHSlot
  /-- The optional fourth Diffie-Hellman slot. -/
  dh4 : Option DHSlot
  /-- The Kyber secret. -/
  ss : Key

/-- The challenge input that the adversary names: literal DH1, DH2 and Kyber secret, and an
optional one-time prekey `Y4`. The game fills DH3 with `agree(a, B)` and DH4 with `agree(a, Y4)`. -/
structure ODHChallenge where
  /-- The literal first Diffie-Hellman value. -/
  dh1 : Key
  /-- The literal second Diffie-Hellman value. -/
  dh2 : Key
  /-- The one-time prekey of the fourth slot, if any. -/
  opk : Option ECPub
  /-- The literal Kyber secret. -/
  ss : Key

open Classical in
/-- The 32 bytes that the extracted agreement of `sk` with `Y` returns, or `none` when it returns
an error, a value of another length, or does not return. -/
def agreeKey (sk : ECPriv) (Y : ECPub) : Option Key :=
  if h : ∃ k : Key, curve.PrivateKey.calculate_agreement sk Y = .ok (.Ok k.to_slice) then
    some (Classical.choose h)
  else none

/-- The value of a slot for the embedded key pairs `a` and `b`. -/
def DHSlot.eval (a b : ECKeyPair) : DHSlot → Option Key
  | .lit v => some v
  | .agreeA Y => agreeKey a.private_key Y
  | .agreeB Y => agreeKey b.private_key Y

/-- The complete key-derivation input of a template, or `none` when one of its agreements does
not return 32 bytes. -/
def KdfTemplate.eval (a b : ECKeyPair) (t : KdfTemplate) : Option (List U8) := do
  let d1 ← t.dh1.eval a b
  let d2 ← t.dh2.eval a b
  let d3 ← t.dh3.eval a b
  let d4 ← match t.dh4 with
    | none => pure none
    | some s => some <$> s.eval a b
  pure (kdfInputBytes d1 d2 d3 d4 t.ss)

/-- The complete key-derivation input of the challenge: DH3 is `agree(a, B)` and DH4 is
`agree(a, Y4)`. -/
def ODHChallenge.eval (a b : ECKeyPair) (c : ODHChallenge) : Option (List U8) :=
  KdfTemplate.eval a b
    { dh1 := .lit c.dh1, dh2 := .lit c.dh2, dh3 := .agreeA b.public_key,
      dh4 := c.opk.map .agreeA, ss := c.ss }

/-- The oracles of the PQXDH oracle Diffie-Hellman game: uniform sampling and the key derivation
on a template. -/
abbrev ODHOracleSpec := unifSpec + (KdfTemplate →ₒ Option (Key × Key × Key))

/-- An adversary against the PQXDH oracle Diffie-Hellman game. From the two public keys and with
the oracles, it names a challenge. Given the challenge keys and with the oracles, it outputs a
bit. -/
structure PqxdhODHAdversary where
  /-- The adversary's state between its two stages. -/
  State : Type
  /-- The first stage: name the challenge. -/
  pre : ECPub → ECPub → OracleComp ODHOracleSpec (ODHChallenge × State)
  /-- The second stage: output a bit. -/
  post : State → Option (Key × Key × Key) → OracleComp ODHOracleSpec Bool

/-- The key-derivation oracle for the embedded key pairs `a` and `b`. It returns the derived keys
of a template's complete input and records the input. It returns `none` when the input cannot be
formed, and it refuses the input `refused` by returning `none`. -/
def odhImpl (H : crypto.HmacSha256) (a b : ECKeyPair) (refused : Option (List U8)) :
    QueryImpl ODHOracleSpec (StateT (List (List U8)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (List (List U8)) ProbComp) +
    fun t : KdfTemplate =>
      (match t.eval a b with
        | none => pure none
        | some inp =>
            if refused = some inp then pure none
            else do
              modify (inp :: ·)
              pure (some (kdfOfBytes H inp)) :
        StateT (List (List U8)) ProbComp (Option (Key × Key × Key)))

/-- The PQXDH oracle Diffie-Hellman game, real (`real = true`) or random. Draw the two key pairs
`a` and `b` from `P.ecKeygen` and give the adversary their public keys. The adversary names a
challenge input. If that input can be formed, the adversary receives either the derived keys of
that input (real) or three uniform keys (random). Otherwise it receives `none` in both worlds.
Throughout, it can ask for the derived keys of any template. After the challenge, the oracle
refuses the challenge's complete input, and if an earlier query had that input, the game outputs
`false` in both worlds. The oracle refuses by complete input, not by point: X25519 reads only the
u-coordinate of a public key, so another encoding of a point gives the same agreement, and Bob
does not check the public key of DH1 for canonicality (`rust/protocol/src/pqxdh.rs:350-355`). -/
def pqxdhODHExp (H : crypto.HmacSha256) (P : Params Rand Msg C IdC IdK) (A : PqxdhODHAdversary)
    (real : Bool) : ProbComp Bool := do
  let a ← P.ecKeygen
  let b ← P.ecKeygen
  let ((c, st), log) ← (simulateQ (odhImpl H a b none) (A.pre a.public_key b.public_key)).run []
  match c.eval a b with
  | none => (simulateQ (odhImpl H a b none) (A.post st none)).run' log
  | some inp => do
      let key ← if real then pure (kdfOfBytes H inp) else $ᵗ (Key × Key × Key)
      let g ← (simulateQ (odhImpl H a b (some inp)) (A.post st (some key))).run' log
      pure (decide (inp ∉ log) && g)

/-- The PQXDH oracle Diffie-Hellman advantage: the distance between the probabilities that
the adversary outputs `true` in the real and in the random game. This is the mmPRF-ODH notion of
Brendel, Fischlin, Günther and Janson (CRYPTO 2017), with oracles on both embedded keys, adapted
to the PQXDH input layout and to X25519 encodings. They show that it holds in the random-oracle
model under the strong Diffie-Hellman assumption, and that no standard-model proof is expected.
Like every premise here, it bounds adversaries without a resource bound (#41). -/
def pqxdhODHAdvantage (H : crypto.HmacSha256) (P : Params Rand Msg C IdC IdK)
    (A : PqxdhODHAdversary) : ℝ :=
  |(Pr[= true | pqxdhODHExp H P A true]).toReal - (Pr[= true | pqxdhODHExp H P A false]).toReal|

end ODH

section Kyber

/-- The bridge contract for Kyber. The abstract KEM `K` describes the extracted Kyber operations:
* `P.pqKeygen` is `K`'s key generation;
* `K`'s encapsulation is a function `encDet` of the public key and of the generator state drawn
  from `P.coins`, and its decapsulation is a function `decDet`;
* every extracted encapsulation on a 1568-byte key, and every extracted decapsulation with a
  secret key from `P.pqKeygen`, either faults or returns what `encDet` or `decDet` gives, where a
  returned error stands for no key.

The bridge claims no termination. `KyberPartial` covers the branches on keys of other lengths. -/
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
