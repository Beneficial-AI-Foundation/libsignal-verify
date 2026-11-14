/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.Models.PQXDH.UAKE.SecurityLemmas

/-!
# Security Theorems for the PQXDH model

We model UAKE security of the model by bounding the adversary's advantage in the
UAKE game based on its advantage in the security games of the underlying
cryptographic primitives.

Scope of the two theorems
* The premises on the primitives (`hsig`, `hgap`, `hkem`, `haead`, `hkdf`) quantify over
  all adversaries, with no resource bound (#41). An unbounded adversary breaks each
  primitive, so each premise holds only when its `ε` is close to the largest advantage of
  its game. The theorems are true implications that do not yet express computational
  security. That needs the resource model of #41.
* `hkemCorrect` (perfect KEM correctness) is an idealization, because production Kyber
  decapsulates wrongly with a small probability. Only the PQ hops 5 and 6 use it, and their
  proofs must replace it (see their docstrings).
* The experiment is the partnered experiment `PartneredExp` over original-key partnering
  (`originalKeyPartnering`). Alice's challenge session and a session of Bob are partners when both
  have accepted with the same associated data and the same key material `km`, the input of the
  KDF. Alice wins outright when she accepts and no session of Bob that accepted no later than she
  did is her partner. The key identifiers, the signatures and the bytes of an unsigned one-time
  pre-key are not authenticated: changing them without changing `km` keeps the partner. These
  theorems do not use the transcript matching of `UAKE.Exp`, because under transcript matching a
  run that changes only unsigned key identifiers counts as a forgery (#35).
  `uakeInitiator_advantage_eq_keyOnly` shows that keeping the session contexts leaves the
  advantage in `UAKE.Exp` unchanged. Transcript matching and original-key partnering are two
  instances of the session-level experiment `SessionExp`: `sessionAdvantage_transcript` gives
  `UAKE.advantage`, and `sessionAdvantage_toSession` gives `partneredAdvantage`.

Model simplifications
* **Unilateral authentication:** UAKE is unilaterally authenticated. In
  principle, it should be possible to model a protocol in both directions to
  show multilateral authentication. However, we model security only for the
  "Bob authenticates to Alice" direction. This is because UAKE security
  requires explicit authentication, and Alice's authentication to Bob is
  implicit via the adversary being unable to compute the DH output, rather than
  relying on Alice's signature (she signs nothing). The other direction,
  `uakeRecipient`, is correctness-only and has no advantage statement here.
* **Joint EUF-CMA of the identity key:** One identity key signs and does
  Diffie-Hellman. The premise `hsig` is joint EUF-CMA: it bounds an adversary in the game of
  `SignatureAlg.jointUnforgeableExp`, which is EUF-CMA with an extra oracle on the same secret
  key. The adversary has signing queries and agreement queries `Y ↦ DH x Y` on the same key
  pair, and it wins with a valid signature on a message that it never had signed. The security
  statements assume this and not SUF-CMA, the strong notion that also counts a new signature on
  a signed message. XEdDSA lacks SUF-CMA because its signature encoding is not unique:
  libsignal's verifier reduces `s` modulo the group order `ℓ`, so `(R, s + ℓ)` also verifies
  when `s + ℓ < 2^253` (`rust/core/src/curve/curve25519.rs:134-155`). The authentication
  argument needs only that no one signs a new message without the key, which is EUF-CMA. The
  joint form adds the Diffie-Hellman oracle because the identity key also does agreement. Bao,
  Pan and Zeng analyse XEdDSA under a related notion with a Diffie-Hellman decision oracle
  (Section 5.1, Theorem 5 of "Better Security Proofs for X3DH and XHMQV"). The signature
  forgery event therefore compares signed keys and not signature bytes. A run in which the
  adversary only changes a signature on an honestly signed key is no signature forgery. Such a
  run keeps `ad` and `km`, so Alice keeps her original-key partner, and the run is in no forgery
  event. See Li & Schäge, "No-Match Attacks and Robust Partnering Definitions" (ACM CCS 2017)
  for attacks of this kind.
* **PQ-secure signature scheme:** In order to re-use our AKE definition in the
  post-quantum case, we assume here that the signature scheme is *still
  secure*, even in the post-quantum setting. In reality, PQXDH uses an EC-based
  signature scheme, which is insecure against a quantum adversary. This is not
  a problem for the protocol, since the desired PQ security is security against
  HNDL attacks, which requires only secrecy, not integrity. However, UAKE
  cannot capture secrecy alone. A better way to model this kind of security
  would be to use a secrecy-only definition.
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

namespace Protocols.Models.PQXDH

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}

/-- Top-level UAKE security theorem for the PQXDH model, assuming the
  underlying DH key exchange is hard to break. The advantage is that of the partnered
  experiment over original-key partnering (`originalKeyPartnering`). This models UAKE
  security in the non-PQ setting. The module note describes the scope of its premises. -/
theorem uakeInitiator_secure_dh
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited F]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq SS] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    /- Any UAKE adversary that opens at most q sessions with its T oracle in each of its two
      stages, so at most 2 * q in all. -/
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    /- Probabilities bounding the adversary's advantage w/r/t PQXDH's component
      primitives. -/
    (εsig εgap εaead εkdf εpk : ℝ)
    /- We assume the signature scheme has a deterministic verification
      procedure. This holds in general for signature schemes, but VCV-io's
      signature scheme definition leaves it monadic, so this seems to be a
      modeling gap. -/
    (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- Bound on an adversary's advantage in forging a signature, in the game with the
      one identity key that signs and does Diffie-Hellman: the adversary has signing
      queries and agreement queries on the same key pair, and wins with a valid
      signature on a message that it never had signed. -/
    (hsig : ∀ B : P.sig.JointAdversary (DH : F → G → G), B.advantage.toReal ≤ εsig)
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
      ((kdfPRFDH P).prfAdvantage D).toReal ≤ εkdf)
    /- Bound on the probability of guessing the public key output by the KEM's
      key generation. This bounds KEM public-key collisions and predictions
      across T-oracle sessions, which otherwise seem to break UAKE security. -/
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    /- Top-level theorem statement: The adversary's advantage in the UAKE game
      is bounded as a polynomial over the adversary bounds of the underlying
      schemes, where the coefficients are small constants and the number q of
      sessions started with its T oracle. -/
    partneredAdvantage ProbCompRuntime.probComp (originalKeyPartnering P msg hasOPK) A ≤
      εsig + 2 * q * (εgap + 2 * εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk := by
  have h₀ := advantage_le_forgeProb_add_indistAdvantage P msg hasOPK A
  have h₁ := forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood P msg hasOPK A
  have h₂ := sigForgeProb_le_sig P msg hasOPK A εsig hverifyDet hsig
  have h₃ := pqpkGuessedProb_le P msg hasOPK A q hq εpk hpk
  have h₄ := forgeHonestGoodProb_le_gap P msg hasOPK A q hq εgap εaead εkdf hgap haead hkdf
  have h₅ := indistAdvantage_le_gap P msg hasOPK A q hq εgap εaead εkdf εpk hgap haead hkdf hpk
  have hεaead : (0 : ℝ) ≤ εaead :=
    le_trans ENNReal.toReal_nonneg (haead ⟨pure ()⟩)
  have hqa : (0 : ℝ) ≤ (q : ℝ) * εaead := mul_nonneg (Nat.cast_nonneg q) hεaead
  nlinarith [h₀, h₁, h₂, h₃, h₄, h₅, hqa]

/-- Top-level UAKE security theorem for the PQXDH model, making no assumptions
  about the underlying DH key exchange, but assuming the KEM is secure. The advantage is
  that of the partnered experiment over original-key partnering (`originalKeyPartnering`).
  This models UAKE security in the PQ setting.
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

  The module note describes the scope of its premises. -/
theorem uakeInitiator_secure_pq
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [SampleableType SS] [DecidableEq SS]
    [Inhabited S] [Inhabited F] [Inhabited PQSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    /- Any UAKE adversary that opens at most q sessions with its T oracle in each of its two
      stages, so at most 2 * q in all. -/
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    /- Probabilities bounding the adversary's advantage w/r/t PQXDH's component
      primitives. -/
    (εsig εkem εaead εkdf εpk : ℝ)
    /- We assume the signature scheme has a deterministic verification
      procedure. This holds in general for signature schemes, but VCV-io's
      signature scheme definition leaves it monadic, so this seems to be a
      modeling gap. -/
    (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- We assume the KEM is perfectly correct (an idealization; see the module note). -/
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    /- Bound on an adversary's advantage in forging a signature, in the game with the
      one identity key that signs and does Diffie-Hellman: the adversary has signing
      queries and agreement queries on the same key pair, and wins with a valid
      signature on a message that it never had signed.
      * MODEL SIMPLIFICATION: In order to re-use our AKE definition, we assume
        here that the signature scheme is *still secure*, even in the
        post-quantum setting. In reality, PQXDH uses an EC-based signature
        scheme, which is insecure against a quantum adversary. This is not a
        problem for the protocol, since the desired PQ security is security
        against HNDL attacks, which requires only secrecy, not integrity.
        However, UAKE cannot capture secrecy alone. A better way to model this
        kind of security would be to use a secrecy-only definition. -/
    (hsig : ∀ B : P.sig.JointAdversary (DH : F → G → G), B.advantage.toReal ≤ εsig)
    /- Bound on an adversary's advantage in the IND-CCA game for the KEM. -/
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      (P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    /- Bound on the adversary's advantage forging an AEAD ciphertext. -/
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- Bound on an adversary's distinguishing advantage for the KDF, modeled as
      a PRF.
      * MODEL SIMPLIFICATION: We model the KDF as a PRF keyed by the KEM
        secret. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      ((kdfPRF P).prfAdvantage D).toReal ≤ εkdf)
    /- Bound on the probability of guessing the public key output by the KEM's
      key generation. This bounds KEM public-key collisions and predictions
      across T-oracle sessions, which otherwise seem to break UAKE security. -/
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    /- Top-level theorem statement: The adversary's advantage in the UAKE game
      is bounded as a polynomial over the adversary bounds of the underlying
      schemes, where the coefficients are small constants and the number q of
      sessions started with its T oracle. -/
    partneredAdvantage ProbCompRuntime.probComp (originalKeyPartnering P msg hasOPK) A ≤
      εsig + 2 * q * (εkem + εaead + εkdf) + 3 * (q : ℝ) ^ 2 * εpk := by
  have h₀ := advantage_le_forgeProb_add_indistAdvantage P msg hasOPK A
  have h₁ := forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood P msg hasOPK A
  have h₂ := sigForgeProb_le_sig P msg hasOPK A εsig hverifyDet hsig
  have h₃ := pqpkGuessedProb_le P msg hasOPK A q hq εpk hpk
  have h₄ := forgeHonestGoodProb_le_pq P msg hasOPK A q hq εkem εaead εkdf hkemCorrect hkem
    haead hkdf
  have h₅ := indistAdvantage_le_pq P msg hasOPK A q hq εkem εkdf εpk hkemCorrect hkem hkdf hpk
  nlinarith [h₀, h₁, h₂, h₃, h₄, h₅]

end Protocols.Models.PQXDH
