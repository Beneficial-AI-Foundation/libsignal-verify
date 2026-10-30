/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.PQXDH.Realization.SecurityDefs

/-!
# Security of the Full realization

Two statements bound the advantage of every adversary against the Full realization
`uakeInitiator` on the extracted entry points, in which Bob is the authenticated party:
* `uakeInitiator_secure_dh`, in the classical setting, from an oracle Diffie-Hellman assumption on
  the protocol's own Diffie-Hellman values and key derivation;
* `uakeInitiator_secure_pq`, in a post-quantum setting, from the security of Kyber with no
  Diffie-Hellman assumption.

## The experiment

The experiment is the UAKE experiment of Dodis and Fiore over **original-key partnering**
(`PartneredExp` with `fullPartnering`). The adversary runs sessions of Bob through oracles and
plays Alice's challenge session.

* The adversary wins outright when the challenge accepts and no session of Bob that accepted no
  later than the challenge holds the same associated data and the same original key material
  `km`. Partnering binds the key material and the associated data, not the bytes of every
  message. Unsigned one-time-prekey bytes and key identifiers are not authenticated.
* The adversary's only exposure query reveals the key of a completed session of Bob. A challenge
  with a revealed partner is not fresh, and the experiment replaces the adversary's guess by a
  coin flip. There is no corruption of long-term keys and no reveal of session state.
* The adversary opens at most `q` sessions of Bob in each of its two stages
  (`OpensAtMostPerPhase`), so at most `2q` in all.
* `partneredAdvantage` is the distance of the probability that the experiment returns `true` from
  `1/2`.

## Scoring of faults

A panic or a non-terminating call of extracted code is missing probability mass in the experiment
(`RustOracleComp`). Each statement bounds the advantage by the primitive terms plus the
probability `Pr[⊥]` that the experiment faults. This form is true whether or not some opaque leaf
can fault, because a fault that no contract excludes only enlarges `Pr[⊥]`. So the premises are
the fault-or-value contracts (`PartialContracts`), which say what a leaf returns when it returns
and claim no termination.

`fullExp_noLostMass` states that the experiment loses no mass under the total contracts on every
leaf, RNG totality, and an adversary that sends only messages fitting in memory. The corollaries
`uakeInitiator_secure_dh_total` and `uakeInitiator_secure_pq_total` combine it with each statement
into a bound without the `Pr[⊥]` term.

## Premises

* the fault-or-value contracts, for an HMAC interface `H` from which the key derivation is built;
* valid curve25519 pairs and Kyber1024-shaped pairs from the ideal generators (policies);
* joint unforgeability of the single identity key (`jointSigAdvantage`);
* for the DH statement only, the PQXDH oracle Diffie-Hellman assumption on the extracted X25519
  and the key derivation (`pqxdhODHAdvantage`);
* for the PQ statement only, IND-CCA security of an abstract KEM `K` with the Kyber bridge
  contract, and the key derivation as a pseudorandom function keyed by the Kyber secret
  (`kdfPRF`);
* integrity of the synthetic AEAD (`AEAD.INT_CTXT_D_Advantage`);
* a bound on guessing a Kyber public key drawn from `P.pqKeygen`.

The oracle Diffie-Hellman assumption replaces two premises of PQXDH-model, gap Diffie-Hellman and
a key derivation keyed by a fresh public key, which say nothing about the Diffie-Hellman values
that the protocol uses. Otherwise both bounds keep the shape of PQXDH-model's statements. The PQ
statement assumes neither perfect Kyber correctness nor a bound on Kyber's correctness error. A
decapsulation mismatch gives the two parties different keys, and the adversary profits from that
only through the AEAD and key-derivation terms.

## Limits

* The premises bound the advantage of every adversary, with no resource bound (#41). Against
  computationally unbounded adversaries they hold only with large constants, so the statements
  are not yet meaningful computational security.
* The PQ statement models post-quantum security as UAKE security without the Diffie-Hellman
  assumption. It still assumes the signature premise, and joint unforgeability with an agreement
  oracle implies that discrete logarithms are hard for the identity key. This is PQXDH-model's
  model gap, made sharper by the single key.
* The wrapper (bundle as a message from Bob, synthetic AEAD, Bob's confirmation) is not extracted
  code (see `Scheme.lean`).

The proofs of the two statements and of `fullExp_noLostMass` are stubs. They are placeholders for
the security milestone, and `Protocols/LEDGER.md` lists them apart from the admitted hops.
-/

open OracleSpec OracleComp AKE AKE.UAKE ENNReal
open Aeneas Aeneas.Std
open libsignal_protocol
open Protocols.Realization

namespace Protocols.PQXDH.Realization

noncomputable section

variable {Rand Msg C IdC IdK : Type}
  [DecidableEq Msg] [DecidableEq C] [DecidableEq IdC] [DecidableEq IdK]

/-- The Full experiment against the adversary `A`: the partnered UAKE experiment of
`uakeInitiator` on the extracted entry points, under the runtime of `RustOracleComp`. -/
abbrev fullExp (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK)) :
    RustOracleComp unifSpec Bool :=
  PartneredExp rustRuntime.toProbCompLift (fullPartnering P EntryPoints.extracted msg hasOPK) A

/-- The advantage of `A` against the Full realization. -/
abbrev fullAdvantage (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (A : UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK)) : ℝ :=
  partneredAdvantage rustRuntime (fullPartnering P EntryPoints.extracted msg hasOPK) A

/-- Security of the Full realization in the classical setting: for every adversary that opens at
most `q` sessions of Bob in each stage, its advantage is at most
`εsig + 2q (εodh + 2 εaead) + 3 q² εpk` plus the probability that the experiment faults.

The premises are the fault-or-value contracts for the HMAC interface `H`, valid curve25519 pairs
and Kyber1024-shaped pairs from the ideal generators, joint unforgeability of the identity key
(`εsig`), the PQXDH oracle Diffie-Hellman assumption on the extracted X25519 and the key
derivation (`εodh`), AEAD integrity (`εaead`) and Kyber public-key guessing (`εpk`). The oracle
Diffie-Hellman assumption holds in the random-oracle model under the strong Diffie-Hellman
assumption, and no standard-model proof is expected. Like every premise here, it bounds
adversaries without a resource bound (#41). The proof is a stub, a placeholder for the security
milestone. -/
theorem uakeInitiator_secure_dh (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (H : crypto.HmacSha256) (hC : PartialContracts H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (A : UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK)) (q : ℕ)
    (hq : A.OpensAtMostPerPhase q)
    (εsig εodh εaead εpk : ℝ)
    (hsig : ∀ B : JointSigAdversary, (jointSigAdvantage P B).toReal ≤ εsig)
    (hodh : ∀ D : PqxdhODHAdversary, pqxdhODHAdvantage H P D ≤ εodh)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead, AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hpk : ∀ pk : PQPub, (Pr[= pk | (·.public_key) <$> P.pqKeygen]).toReal ≤ εpk) :
    fullAdvantage P msg hasOPK A ≤
      εsig + 2 * q * (εodh + 2 * εaead) + 3 * (q : ℝ) ^ 2 * εpk +
        (Pr[⊥ | rustRuntime.evalDist (fullExp P msg hasOPK A)]).toReal := by
  sorry

/-- Security of the Full realization in the post-quantum setting: for every adversary that opens
at most `q` sessions of Bob in each stage, its advantage is at most
`εsig + 2q (εkem + εaead + εkdf) + 3 q² εpk` plus the probability that the experiment faults.

The premises are those of `uakeInitiator_secure_dh` without the Diffie-Hellman assumption,
together with IND-CCA security of an abstract KEM `K` (`εkem`) that the Kyber bridge contract
ties to the extracted Kyber calls, and the key derivation as a pseudorandom function keyed by the
Kyber secret (`εkdf`). No premise concerns Kyber's correctness. The proof is a stub, a
placeholder for the security milestone. -/
theorem uakeInitiator_secure_pq (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (H : crypto.HmacSha256) (hC : PartialContracts H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (K : KEMScheme ProbComp Key PQPub PQPriv (Slice U8)) (hK : KyberBridge P K)
    (A : UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK)) (q : ℕ)
    (hq : A.OpensAtMostPerPhase q)
    (εsig εkem εaead εkdf εpk : ℝ)
    (hsig : ∀ B : JointSigAdversary, (jointSigAdvantage P B).toReal ≤ εsig)
    (hkem : ∀ B : K.IND_CCA_Adversary, K.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead, AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D, (kdfPRF H).prfAdvantage D ≤ εkdf)
    (hpk : ∀ pk : PQPub, (Pr[= pk | (·.public_key) <$> P.pqKeygen]).toReal ≤ εpk) :
    fullAdvantage P msg hasOPK A ≤
      εsig + 2 * q * (εkem + εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk +
        (Pr[⊥ | rustRuntime.evalDist (fullExp P msg hasOPK A)]).toReal := by
  sorry

omit [DecidableEq C] in
/-- The Full experiment loses no mass. Under the total contracts on every opaque leaf
(`CoreContracts`, `SignatureContracts`, `HkdfSha256Contract H`), with Kyber1024-shaped pairs from
`P.pqKeygen` (Bob serializes his own Kyber keys), with both views of the generator total on a
domain that contains every state drawn from `P.coins`, and against an adversary that sends only
messages fitting in memory, the experiment faults with probability `0`. The proof is a stub, a
placeholder for the security milestone. -/
theorem fullExp_noLostMass (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hC : CoreContracts) (hS : SignatureContracts)
    (H : crypto.HmacSha256) (hH : crypto.HkdfSha256Contract H)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r)
    (A : UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK))
    (hA : Adversary.SendsFittingMessages A) :
    Pr[⊥ | rustRuntime.evalDist (fullExp P msg hasOPK A)] = 0 := by
  sorry

/-- Classical security without the fault term: the bound of `uakeInitiator_secure_dh` holds
without `Pr[⊥]` when the premises of `fullExp_noLostMass` also hold. -/
theorem uakeInitiator_secure_dh_total (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (H : crypto.HmacSha256) (hC : PartialContracts H)
    (hCt : CoreContracts) (hS : SignatureContracts) (hH : crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r)
    (A : UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK))
    (hA : Adversary.SendsFittingMessages A) (q : ℕ) (hq : A.OpensAtMostPerPhase q)
    (εsig εodh εaead εpk : ℝ)
    (hsig : ∀ B : JointSigAdversary, (jointSigAdvantage P B).toReal ≤ εsig)
    (hodh : ∀ D : PqxdhODHAdversary, pqxdhODHAdvantage H P D ≤ εodh)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead, AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hpk : ∀ pk : PQPub, (Pr[= pk | (·.public_key) <$> P.pqKeygen]).toReal ≤ εpk) :
    fullAdvantage P msg hasOPK A ≤
      εsig + 2 * q * (εodh + 2 * εaead) + 3 * (q : ℝ) ^ 2 * εpk := by
  have h := uakeInitiator_secure_dh P msg hasOPK H hC hEC hPQ A q hq εsig εodh εaead εpk
    hsig hodh haead hpk
  rwa [fullExp_noLostMass P msg hasOPK hCt hS H hH hPQ Dom hRng hSigRng hCoins A hA,
    ENNReal.toReal_zero, add_zero] at h

/-- Post-quantum security without the fault term: the bound of `uakeInitiator_secure_pq` holds
without `Pr[⊥]` when the premises of `fullExp_noLostMass` also hold. -/
theorem uakeInitiator_secure_pq_total (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (H : crypto.HmacSha256) (hC : PartialContracts H)
    (hCt : CoreContracts) (hS : SignatureContracts) (hH : crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r)
    (K : KEMScheme ProbComp Key PQPub PQPriv (Slice U8)) (hK : KyberBridge P K)
    (A : UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK))
    (hA : Adversary.SendsFittingMessages A) (q : ℕ) (hq : A.OpensAtMostPerPhase q)
    (εsig εkem εaead εkdf εpk : ℝ)
    (hsig : ∀ B : JointSigAdversary, (jointSigAdvantage P B).toReal ≤ εsig)
    (hkem : ∀ B : K.IND_CCA_Adversary, K.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead, AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D, (kdfPRF H).prfAdvantage D ≤ εkdf)
    (hpk : ∀ pk : PQPub, (Pr[= pk | (·.public_key) <$> P.pqKeygen]).toReal ≤ εpk) :
    fullAdvantage P msg hasOPK A ≤
      εsig + 2 * q * (εkem + εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk := by
  have h := uakeInitiator_secure_pq P msg hasOPK H hC hEC hPQ K hK A q hq εsig εkem εaead εkdf
    εpk hsig hkem haead hkdf hpk
  rwa [fullExp_noLostMass P msg hasOPK hCt hS H hH hPQ Dom hRng hSigRng hCoins A hA,
    ENNReal.toReal_zero, add_zero] at h

end

end Protocols.PQXDH.Realization
