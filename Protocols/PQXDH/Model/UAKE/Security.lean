/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.SecurityLemmas

/-!
# Security Theorems for the PQXDH model

We model UAKE security of the model by bounding the adversary's advantage in the
UAKE game based on its advantage in the security games of the underlying
cryptographic primitives.

Model simplifications
* **Unilateral authentication:** UAKE is unilaterally authenticated. In
  principle, it should be possible to model a protocol in both directions to
  show multilateral authentication. However, we model security only for the
  "Bob authenticates to Alice" direction. This is because UAKE security
  requires explicit authentication, and Alice's authentication to Bob is
  implicit via the adversary being unable to compute the DH output, rather than
  relying on Alice's signature (she signs nothing).
  The opposite direction (`uakeRecipient`, built from `initiatorNoConfirm` and
  `recipientNoConfirm`) is correctness-only: it has correctness and
  well-formedness theorems, and no advantage statement and no partnering. Its
  unkeyed party's input holds Bob's long-term secret state, which
  `challengeSession` hands to the adversary, and PQXDH gives the initiator no
  explicit authentication. Generic functions still accept the scheme, so this
  scope is enforced by documentation and not by types.
* **SUF-CMA signature (not EUF-CMA):** Since UAKE is a
  transcript-matching-style definition, our security theorems are subject to
  harmless but definition-breaking "no-match" attacks on the signature scheme.
  See Li & Schäge, "No-Match Attacks and Robust Partnering Definitions" (ACM CCS
  2017) for a reference on attacks of this kind.
* **PQ-secure signature scheme:** In order to re-use our AKE definition in the
  post-quantum case, we assume here that the signature scheme is *still
  secure*, even in the post-quantum setting. In reality, PQXDH uses an EC-based
  signature scheme, which is insecure against a quantum adversary. This is not
  a problem for the protocol, since the desired PQ security is security against
  HNDL attacks, which requires only secrecy, not integrity. However, UAKE
  cannot capture secrecy alone. A better way to model this kind of security
  would be to use a secrecy-only definition.
* **Injective key→ID maps:** We assume that the function mapping KEM keys to
  identifiers is injective. Section 4.13 of the spec contains the weaker
  requirement that "collisions are unlikely". Modeling the maps as collision
  resistant would be an improvement, since it would allow a hash of the key to
  be used, but we leave that as a future improvement.
* **PQ security as UAKE with PQ signature:** We model PQ security as "UAKE
  security with compromised DH key exchange." This allows us to reuse our UAKE
  notion, but it's not quite the desired statement of security. In a PQ
  setting, PQXDH is intended to be resistant to harvest-now-decrypt-later
  (HNDL) attacks, *not* a general authenticated key exchange notion. The
  difference is that, although key secrecy should be maintained, authenticity
  doesn't need to be. However, UAKE doesn't allow us to argue about key secrecy
  in isolation. Moreover, in order to show the authenticity part of UAKE, we
  must assume that the signature scheme is PQ secure, which is not the case for
  PQXDH in practice. The way to fix this would be to use a dedicated HNDL
  security notion here, rather than UAKE, and omit the hypothesis that the
  signature scheme is secure.
* **KDF modeled as a PRF in non-PQ security:** We currently model the KDF as a
  PRF in both the PQ and non-PQ security theorems. The previous CryptoVerif
  analysis uses a random oracle to model the KDF in the non-PQ case, so it may
  be necessary for us to do this as well in order to complete the proof.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

/-- Top-level UAKE security theorem for the PQXDH model, assuming the
  underlying DH key exchange is hard to break. This models UAKE security in the
  non-PQ setting.

  The premises `hsig`, `hgap`, `haead` and `hkdf` quantify over all adversaries with
  no resource bound (issue #41). A computationally unbounded adversary breaks each
  primitive, so each premise holds only for an `ε` close to the largest advantage its game
  allows. The theorem is a true implication that does not yet express computational
  security. That needs the resource model of #41. -/
theorem uakeInitiator_secure_dh
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq SS] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    /- PREMISE FALSE FOR PRODUCTION. We assume the function mapping KEM keys to key
      identifiers is injective. Production identifiers are 32-bit prekey ids, and no map
      from 1568-byte KEM public keys to a 32-bit space is injective. The premise is kept
      until it is removed with the restatement of hop 5. Issue #35 reports the underlying
      problem: unsigned key identifiers break transcript matching. -/
    (hidKEM : Function.Injective P.idKEM)
    /- Any UAKE adversary who starts at most q sessions with its T oracle. -/
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    /- Probabilities bounding the adversary's advantage w/r/t PQXDH's component
      primitives. -/
    (εsig εgap εaead εkdf εpk : ℝ)
    /- We assume the signature scheme has a deterministic verification
      procedure. This holds in general for signature schemes, but VCV-io's
      signature scheme definition leaves it monadic, so this seems to be a
      modeling gap. -/
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- Bound on an adversary's advantage in forging a signature.
      * DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
        just EUF-CMA. This is required to avoid (harmless) LS'17-style
        "no-match" attacks because we use a transcript-matching AKE definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    /- Bound on an adversary's advantage in the DH security game. -/
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    /- Bound on the adversary's advantage forging an AEAD ciphertext. -/
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- Bound on an adversary's distinguishing advantage for the KDF, modeled as
      a PRF.
      * MODEL SIMPLIFICATION: We model the KDF as a PRF. Since we key our KDF
        using DH group elements, we must also assume that the KDF is secure
        when keyed with one of these, rather than a random bit string.
      * NOTE: It may be necessary to model this as a random oracle, instead of
        a PRF, in order to complete the proof. The previous CryptoVerif
        analysis uses a RO here. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf)
    /- Bound on the probability of guessing the public key output by the KEM's
      key generation. This bounds KEM public-key collisions and predictions
      across T-oracle sessions, which otherwise seem to break UAKE security. -/
    (hpk : ∀ pk : PQPK, (Pr[= pk | Prod.fst <$> P.pqkem.keygen]).toReal ≤ εpk) :
    /- Top-level theorem statement: The adversary's advantage in the UAKE game
      is bounded as a polynomial over the adversary bounds of the underlying
      schemes, where the coefficients are small constants and the number q of
      sessions started with its T oracle. -/
    UAKE.advantage ProbCompRuntime.probComp A ≤
      εsig + 2 * q * (εgap + 2 * εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk := by
  have h₀ := advantage_le_forgeProb_add_indistAdvantage P msg hasOPK A
  have h₁ := forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood P msg hasOPK A
  have h₂ := sigForgeProb_le_sig P msg hasOPK A εsig hverifyDet hsig
  have h₃ := pqpkGuessedProb_le P msg hasOPK A q hq εpk hpk
  have h₄ := forgeHonestGoodProb_le_gap P msg hasOPK A q hq εgap εaead εkdf hidKEM hgap
    haead hkdf
  have h₅ := indistAdvantage_le_gap P msg hasOPK A q hq εgap εaead εkdf εpk hidKEM hgap
    haead hkdf hpk
  have hεaead : (0 : ℝ) ≤ εaead :=
    le_trans ENNReal.toReal_nonneg (haead ⟨pure ()⟩)
  have hqa : (0 : ℝ) ≤ (q : ℝ) * εaead := mul_nonneg (Nat.cast_nonneg q) hεaead
  nlinarith [h₀, h₁, h₂, h₃, h₄, h₅, hqa]

/-- Top-level UAKE security theorem for the PQXDH model, making no assumptions
  about the underlying DH key exchange, but assuming the KEM is secure. This
  models UAKE security in the PQ setting.
  * MODEL GAP: We model PQ security here as "UAKE security with compromised DH
    key exchange." This allows us to reuse our UAKE notion, but it's not quite
    the desired statement of security. In a PQ setting, PQXDH is intended to be
    resistant to harvest-now-decrypt-later (HNDL) attacks, *not* a general
    authenticated key exchange notion. The difference is that, although key
    secrecy should be maintained, authenticity doesn't need to be. However,
    UAKE doesn't allow us to argue about key secrecy in isolation. Moreover, in
    order to show the authenticity part of UAKE, we must assume that the
    signature scheme is PQ secure, which is not the case for PQXDH in practice.
    The way to fix this would be to use a dedicated HNDL security notion here,
    rather than UAKE, and omit the hypothesis that the signature scheme is
    secure.

  The premises `hsig`, `hkem`, `haead` and `hkdf` quantify over all adversaries with
  no resource bound (issue #41). A computationally unbounded adversary breaks each
  primitive, so each premise holds only for an `ε` close to the largest advantage its game
  allows. The theorem is a true implication that does not yet express computational
  security. That needs the resource model of #41. -/
theorem uakeInitiator_secure_pq
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [SampleableType SS] [DecidableEq SS]
    [Inhabited S] [Inhabited SSK] [Inhabited PQSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    /- PREMISE FALSE FOR PRODUCTION. We assume the function mapping KEM keys to key
      identifiers is injective. Production identifiers are 32-bit prekey ids, and no map
      from 1568-byte KEM public keys to a 32-bit space is injective. The premise is kept
      until it is removed with the restatement of hop 5. Issue #35 reports the underlying
      problem: unsigned key identifiers break transcript matching. -/
    (hidKEM : Function.Injective P.idKEM)
    /- Any UAKE adversary who starts at most q sessions with its T oracle. -/
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    /- Probabilities bounding the adversary's advantage w/r/t PQXDH's component
      primitives. -/
    (εsig εkem εaead εkdf εpk : ℝ)
    /- We assume the signature scheme has a deterministic verification
      procedure. This holds in general for signature schemes, but VCV-io's
      signature scheme definition leaves it monadic, so this seems to be a
      modeling gap. -/
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- IDEALIZATION. We assume the KEM is perfectly correct. This is false for production
      Kyber, whose decapsulation can return a different shared secret with a small nonzero
      probability. This theorem is therefore not instantiated at production Kyber. The
      premise is kept as a labelled idealization until it is replaced by an explicit
      mismatch-event term or removed. -/
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    /- Bound on an adversary's advantage in forging a signature.
      * DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
        just EUF-CMA. This is required to avoid (harmless) LS'17-style
        "no-match" attacks because we use a transcript-matching AKE definition.
      * MODEL SIMPLIFICATION: In order to re-use our AKE definition, we assume
        here that the signature scheme is *still secure*, even in the
        post-quantum setting. In reality, PQXDH uses an EC-based signature
        scheme, which is insecure against a quantum adversary. This is not a
        problem for the protocol, since the desired PQ security is security
        against HNDL attacks, which requires only secrecy, not integrity.
        However, UAKE cannot capture secrecy alone. A better way to model this
        kind of security would be to use a secrecy-only definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    /- Bound on an adversary's advantage in the IND-CCA game for the KEM. -/
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    /- Bound on the adversary's advantage forging an AEAD ciphertext. -/
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- Bound on an adversary's distinguishing advantage for the KDF, modeled as
      a PRF.
      * MODEL SIMPLIFICATION: We model the KDF as a PRF keyed by the KEM
        secret. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      (kdfPRF P).prfAdvantage D ≤ εkdf)
    /- Bound on the probability of guessing the public key output by the KEM's
      key generation. This bounds KEM public-key collisions and predictions
      across T-oracle sessions, which otherwise seem to break UAKE security. -/
    (hpk : ∀ pk : PQPK, (Pr[= pk | Prod.fst <$> P.pqkem.keygen]).toReal ≤ εpk) :
    /- Top-level theorem statement: The adversary's advantage in the UAKE game
      is bounded as a polynomial over the adversary bounds of the underlying
      schemes, where the coefficients are small constants and the number q of
      sessions started with its T oracle. -/
    UAKE.advantage ProbCompRuntime.probComp A ≤
      εsig + 2 * q * (εkem + εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk := by
  have h₀ := advantage_le_forgeProb_add_indistAdvantage P msg hasOPK A
  have h₁ := forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood P msg hasOPK A
  have h₂ := sigForgeProb_le_sig P msg hasOPK A εsig hverifyDet hsig
  have h₃ := pqpkGuessedProb_le P msg hasOPK A q hq εpk hpk
  have h₄ := forgeHonestGoodProb_le_pq P msg hasOPK A q hq εkem εaead εkdf hidKEM
    hkemCorrect hkem haead hkdf
  have h₅ := indistAdvantage_le_pq P msg hasOPK A q hq εkem εkdf εpk hidKEM hkemCorrect
    hkem hkdf hpk
  nlinarith [h₀, h₁, h₂, h₃, h₄, h₅]

end Protocols.PQXDH
