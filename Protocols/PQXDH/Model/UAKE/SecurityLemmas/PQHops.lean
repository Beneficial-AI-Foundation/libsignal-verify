/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.SecurityLemmas.Games

/-!
# IND-CCA Core Hops

Hops 5 and 6 of the PQ security theorem `Protocols.PQXDH.uakeInitiator_secure_pq` in
`Security.lean`: the forgery and indistinguishability cores, against the
KEM's IND-CCA security, the KDF, and the AEAD. See `SecurityLemmas.lean`
for the overall map.

Unlike the GapDH cores, these reductions are expressible in the current
model: the KDF's PRF key slot is an abstract bitstring (the KEM shared
secret) that the game uses only as a KDF key, so once the IND-CCA hop makes
it uniform, the PRF hypothesis applies directly. The proofs are deferred as
future reduction work, with the intended sub-hops recorded in the doc
comments.

The lemma statements and proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- Hop 5 (forgery core, IND-CCA): with an honest bundle and separated KEM
  keys, a forgery requires breaking the KEM, the KDF, or the AEAD.

  Intended proof, as further hops:
  1. Identify the unique T-oracle session that can share the challenge
     session's key material, as in the GapDH core: the accepted bundle pins
     `ikB`, `spkB`, and `pqpkB`, the latter published by exactly one
     session by `hidKEM` and the excluded collision event.
  2. Guess that session among the at most `q` opened (the factor `q`) and
     embed the IND-CCA challenge: its public key becomes the session's
     `pqpkB`, the challenge ciphertext and real-or-random secret stand in
     for the challenge session's encapsulation, the decapsulation oracle
     serves the session's other ciphertexts, and perfect correctness
     (`hkemCorrect`) identifies the session's decapsulation of the
     challenge ciphertext with the encapsulated secret. This replaces the
     challenge session's KEM shared secret with a uniform one (`εkem`).
  3. With the KEM secret uniform, `kdfPRF` is a PRF under a hidden uniform
     key: routing the challenge session's KDF call, and the paired
     session's KDF calls on the challenge ciphertext, through the PRF
     oracle replaces their output triples with a shared random function of
     the DH tuple (`εkdf`).
  4. The AEAD endgame is as in the GapDH core: a tampered initial message
     accepted by the paired session forges against `KA`, and an accepted
     confirmation not produced by the paired session forges against `KB`
     (the two `εaead`); a verbatim relay of honestly produced messages
     forces the global-clock interleaving of `Matching`, so the transcripts
     match, contradicting the forgery event.

  The factor `q` on `εaead` and `εkdf` is generous (only the session guess
  needs it), but stating the bound with it makes the composed bound
  collapse to the signature term when the adversary opens no sessions.

  Used by `uakeInitiator_secure_pq` as hop 5. A proof would follow the steps above in the current
  model, but the last step does not hold as stated, since unsigned bundle fields (the key
  identifiers and the one-time pre-key) can change without changing the derived keys, so the
  transcripts differ with no forgery. -/
lemma forgeHonestGoodProb_le_pq [SampleableType SS] [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εkem εaead εkdf : ℝ)
    (hidKEM : Function.Injective P.idKEM)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      (kdfPRF P).prfAdvantage D ≤ εkdf) :
    forgeHonestGoodProb P msg hasOPK A ≤ q * (εkem + 2 * εaead + εkdf) := by
  sorry

/-- Hop 6 (indistinguishability core, IND-CCA): in `indistExp`, the
  adversary's guess is better than a fair coin only by breaking the KEM or
  the KDF, or by a KEM public-key collision.

  Intended proof, as further hops:
  1. If the challenge session outputs no key, both finalizations hand the
     adversary `none` and the guess is independent of the challenge bit, so
     it wins with probability exactly `1 / 2`; the coined forgery branch
     likewise. Only the ping-pong branch remains.
  2. In the ping-pong branch, the accepted bundle equals a T-oracle
     session's published bundle, so it is honest without a signature
     hypothesis, and the matching session is the paired one.
  3. Replace the challenge session's KEM shared secret with a uniform one
     by the IND-CCA embedding of the forgery core (`q`, `εkem`). By perfect
     correctness the matching session decapsulates the relayed challenge
     ciphertext to the same secret, so, unlike the GapDH core, no
     decapsulation-mismatch AEAD term arises.
  4. Replace the KDF output triple on the challenge session's key material
     with a shared random function of the DH tuple (`εkdf`), as in the
     forgery core.
  5. A reveal query returns the challenge key only for a session with
     identical key material. For a session whose transcript matches the
     challenge, `fullPingPong` flips a fair coin instead; any other such
     session requires two T-oracle sessions sharing a KEM public key.
     Both adversary stages together open at most `2 * q` sessions, giving
     at most `2 * q ^ 2` pairs and the `2 * q ^ 2 * εpk` term by the
     guessing bound (this term also absorbs prediction events in the post
     phase, as in Hop 4).
  6. Otherwise the challenge key is uniform, independent of the adversary's
     view, and unrevealed, so the real and random finalizations are
     identically distributed and the guess wins with probability exactly
     `1 / 2`.

  Used by `uakeInitiator_secure_pq` as hop 6. A proof would follow the steps above in the current
  model. -/
lemma indistAdvantage_le_pq [SampleableType SS] [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εkem εkdf εpk : ℝ)
    (hidKEM : Function.Injective P.idKEM)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      (kdfPRF P).prfAdvantage D ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr[= pk | Prod.fst <$> P.pqkem.keygen]).toReal ≤ εpk) :
    indistAdvantage P msg hasOPK A ≤
      q * (εkem + εkdf) + 2 * (q : ℝ) ^ 2 * εpk := by
  sorry

end Protocols.PQXDH
