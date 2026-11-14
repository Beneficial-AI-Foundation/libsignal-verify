/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games

/-!
# IND-CCA Core Hops

Hops 5 and 6 of the PQ security theorem `Protocols.Models.PQXDH.uakeInitiator_secure_pq` in
`Security.lean`: the forgery and indistinguishability cores, against the
KEM's IND-CCA security, the KDF, and the AEAD. See `SecurityLemmas.lean`
for the overall map.

Both hops are stated over original-key partnering (`originalKeyPartnering`). The forgery event
of hop 5 is "Alice accepted and no session of Bob is her original-key partner", and `indistExp`
flips a coin on that event and when a revealed session is a partner.

The hop lemmas assume `hkemCorrect`, an idealization. The module note of `Security.lean` gives
the reason.

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

namespace Protocols.Models.PQXDH

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- Hop 5 (forgery core, IND-CCA): with an honest bundle and separated KEM keys, if Alice accepts
  and no session of Bob is her original-key partner, the adversary has broken the KEM, the KDF,
  or the AEAD.

  A session of Bob that completed with a key, holds Alice's associated data and key material
  `(ad, km)`, and accepted no later than Alice is her original-key partner
  (`originalKeyPartnering`). A run that changes the key identifiers, a signature on an honestly
  signed key, or the bytes of the one-time pre-key, and leaves `km` unchanged, keeps that partner,
  so it is not in the event. These fields are not authenticated.

  Intended proof, as further hops:
  1. Identify the session of Bob that can share Alice's key material, as in the GapDH core: the
     accepted bundle pins `ikB`, `spkB` and `pqpkB`, and exactly one session published that KEM
     key, because the excluded collision event makes the published KEM keys distinct. The key
     identifiers play no part.
  2. Guess that session among the at most `q` sessions open when the challenge stage ends
     (`AKE.UAKE.Adversary.OpensAtMost.challengeSession_openCount_le`, the factor `q`) and embed
     the IND-CCA challenge: its public key becomes the session's `pqpkB`, the challenge ciphertext
     and real-or-random secret stand in for Alice's encapsulation, the decapsulation oracle serves
     the session's other ciphertexts, and perfect correctness (`hkemCorrect`) identifies the
     session's decapsulation of the challenge ciphertext with the encapsulated secret. This
     replaces Alice's KEM shared secret with a uniform one (`εkem`).
  3. With the KEM secret uniform, `kdfPRF` is a PRF under a hidden uniform key: routing Alice's KDF
     call, and the guessed session's KDF calls on the challenge ciphertext, through the PRF oracle
     replaces their output triples with a shared random function of the DH tuple (`εkdf`).
  4. The AEAD endgame is as in the GapDH core: a session of Bob that accepts, under Alice's key
     material, a pair of ciphertext and associated data that Alice did not produce forges against
     `KA`, and a confirmation that Alice accepts and that no partner produced forges against `KB`
     (the two `εaead`).

  Steps 3 and 4 must count exposure under `KB` and not deny KDF evaluations. A failed decryption
  may still evaluate the KDF at Alice's key material, distinct inputs need not give distinct KDF
  outputs, and rejection under a wrong key is a security property of the AEAD. These are
  obligations of the proof.

  `hkemCorrect` is an idealization: production Kyber decapsulates wrongly with a small
  probability, so the premise is false for production, and no theorem of this repository
  instantiates this hop at production Kyber. Its replacement in both PQ hops is left to their
  proofs, by one of two routes: a mismatch event with its own proved bound, or a proof that a
  decapsulation mismatch forces a forgery of Bob's confirmation.

  The factor `q` on `εaead` and `εkdf` is generous (only the session guess needs it), but stating
  the bound with it makes the composed bound collapse to the signature term when the adversary
  opens no sessions.

  Used by `uakeInitiator_secure_pq` as hop 5. -/
lemma forgeHonestGoodProb_le_pq [SampleableType SS] [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εkem εaead εkdf : ℝ)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      (P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      ((kdfPRF P).prfAdvantage D).toReal ≤ εkdf) :
    forgeHonestGoodProb P msg hasOPK A ≤ q * (εkem + 2 * εaead + εkdf) := by
  sorry

/-- Hop 6 (indistinguishability core, IND-CCA): in `indistExp`, the adversary's guess is better
  than a fair coin only by breaking the KEM or the KDF, or by a KEM public-key collision.

  `indistExp` is the partnered experiment over `originalKeyPartnering`, with the outright win on
  the forgery event replaced by a fair coin.

  Intended proof, as further hops:
  1. If Alice outputs no key, both finalizations hand the adversary `none` and the guess is
     independent of the challenge bit, so it wins with probability exactly `1 / 2`; the coined
     forgery branch likewise. Only the partnered branch remains.
  2. In the partnered branch, a session of Bob that accepted no later than Alice holds her
     associated data and key material. This does not make the accepted bundle honest, because
     partnering compares `(ad, km)` and not the bundle. Equal key material with a signed pre-key
     other than the one `setup` signed needs degenerate exponents: Alice's identity exponent is
     `0`, and Bob's identity exponent or Alice's ephemeral exponent is `0`. That event has
     probability about `2 / |F| ^ 2` per challenge. The bound has no term for it, and absorbing
     it is an obligation of the proof.
  3. Replace Alice's KEM shared secret with a uniform one by the IND-CCA embedding of the forgery
     core (`q`, `εkem`). The embedding uses perfect correctness (`hkemCorrect`) to answer the
     embedded session's decapsulation of the challenge ciphertext. The partner holds Alice's key
     material, which contains the shared secret, so no decapsulation-mismatch term arises.
  4. Replace the KDF output triple on Alice's key material with a shared random function of the
     DH tuple (`εkdf`), as in the forgery core.
  5. A revealed partner makes `finalizePartnered` flip a fair coin. That includes a second session
     of Bob that published the same KEM key and derives Alice's `(ad, km)` from a replay of her
     initial message. A revealed session that is not a partner returns the challenge key only if
     it derived the same keys from other associated data or other key material, and bounding that
     is an obligation of the proof. The bound keeps the `2 * q ^ 2 * εpk` term, as ported: both
     stages together open at most `2 * q` sessions
     (`AKE.UAKE.Adversary.OpensAtMost.openCount_le_two_mul`), so at most `2 * q ^ 2` pairs of
     sessions can share a KEM public key.
  6. Otherwise the challenge key is uniform, independent of the adversary's view, and unrevealed,
     so the real and random finalizations are identically distributed and the guess wins with
     probability exactly `1 / 2`.

  `hkemCorrect` is an idealization: production Kyber decapsulates wrongly with a small
  probability, so the premise is false for production, and no theorem of this repository
  instantiates this hop at production Kyber. Its replacement in both PQ hops is left to their
  proofs, by one of two routes: a mismatch event with its own proved bound, or a proof that a
  decapsulation mismatch forces a forgery of Bob's confirmation.

  The premises and the bound are those of the ported statement. Used by `uakeInitiator_secure_pq`
  as hop 6. -/
lemma indistAdvantage_le_pq [SampleableType SS] [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εkem εkdf εpk : ℝ)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      (P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      ((kdfPRF P).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    indistAdvantage P msg hasOPK A ≤
      q * (εkem + εkdf) + 2 * (q : ℝ) ^ 2 * εpk := by
  sorry

end Protocols.Models.PQXDH
