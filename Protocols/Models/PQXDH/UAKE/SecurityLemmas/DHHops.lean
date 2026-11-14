/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games
import Protocols.ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# GapDH Core Hops

Hops 5 and 6 of the DH security theorem `Protocols.Models.PQXDH.uakeInitiator_secure_dh` in
`Security.lean`: the forgery and indistinguishability cores, against GapDH,
the KDF, and the AEAD. See `SecurityLemmas.lean` for the overall map.

Both hops are stated over original-key partnering (`originalKeyPartnering`). The forgery event
of hop 5 is "Alice accepted and no session of Bob is her original-key partner", and `indistExp`
flips a coin on that event and when a revealed session is a partner.

These statements are believed true in the current model (the KDF as a plain
parameter function, plus a PRF hypothesis), but the standard reductions
require the KDF to be a programmable random oracle, so their proofs are
deferred to that planned model change; the intended sub-hops are recorded
in the doc comments.

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

/-- Hop 5 (forgery core, GapDH): with an honest bundle and separated KEM keys, if Alice accepts
  and no session of Bob is her original-key partner, the adversary has broken GapDH, the KDF, or
  the AEAD.

  A session of Bob that completed with a key, holds Alice's associated data and key material
  `(ad, km)`, and accepted no later than Alice is her original-key partner
  (`originalKeyPartnering`). A run that changes the key identifiers, a signature on an honestly
  signed key, or the bytes of the one-time pre-key, and leaves `km` unchanged, keeps that partner,
  so it is not in the event. These fields are not authenticated.

  Intended proof, as further hops once the KDF is modeled as a random oracle (see the module
  comment):
  1. Identify the session of Bob that can share Alice's key material: the accepted bundle pins
     `ikB` (checked by Alice), `spkB` (the only EC key `setup` signs) and `pqpkB`. Exactly one
     session published that KEM key, because the excluded collision event makes the published
     KEM keys distinct. The key identifiers play no part.
  2. Replace the KDF output triple `(SK, KA, KB)` on Alice's key material with a fresh uniform
     triple, shared with any session of Bob that derives the same key material. A distinguisher
     must query the KDF on Alice's key material, whose third DH component is `DH ekA.2 spkB.1`
     for her fresh ephemeral `ekA`; embedding the GapDH challenge in `ekA` and `spkB`,
     recognizing the query with the DDH oracle, and answering the T oracle's other KDF queries
     consistently (again via the DDH oracle) yields a GapDH adversary. This step consumes `εgap`
     and, under the current PRF modeling of the KDF, `εkdf`.
  3. With `KA` uniform, a session of Bob that accepts, under Alice's key material, a pair of
     ciphertext and associated data that Alice did not produce forges against `KA` (first
     `εaead`, via the INT-CTXT-D game whose encryption oracle produces Alice's ciphertext).
  4. With `KB` uniform, Alice accepts a confirmation only if it decrypts under `KB` with her
     associated data, and after step 2 only a session of Bob with her key material encrypts
     under `KB`. If such a session produced her confirmation under her associated data, it
     accepted when it sent that confirmation, so no later than Alice, and it is her partner: the
     run is not in the event. Otherwise Alice's acceptance forges against `KB` (second `εaead`).
     This covers a confirmation forged before any session of Bob accepted and relayed to Bob
     afterwards.

  Steps 3 and 4 must count exposure under `KB` and not deny KDF evaluations. A failed decryption
  may still evaluate the KDF at Alice's key material, distinct inputs need not give distinct KDF
  outputs, and rejection under a wrong key is a security property of the AEAD. These are
  obligations of the proof.

  The factor `q` is generous (the reduction handles all sessions at once), but stating the bound
  with it makes the composed bound collapse to `εsig` when the adversary opens no sessions, in
  which case completing the challenge session already requires a signature forgery.

  Used by `uakeInitiator_secure_dh` as hop 5. -/
lemma forgeHonestGoodProb_le_gap [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf : ℝ)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      ((kdfPRFDH P).prfAdvantage D).toReal ≤ εkdf) :
    forgeHonestGoodProb P msg hasOPK A ≤ q * (εgap + 2 * εaead + εkdf) := by
  sorry

/-- Hop 6 (indistinguishability core, GapDH): in `indistExp`, the adversary's guess is better than
  a fair coin only by breaking GapDH, the KDF, or the AEAD, or by a KEM public-key collision.

  `indistExp` is the partnered experiment over `originalKeyPartnering`, with the outright win on
  the forgery event replaced by a fair coin.

  Intended proof, as further hops once the KDF is modeled as a random oracle (see the module
  comment):
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
  3. Replace the KDF output triple on Alice's key material with a fresh uniform triple, as in the
     forgery core (`εgap` plus, under the current PRF modeling, `εkdf`).
  4. The partner holds Alice's key material, so the decapsulation mismatch of the ported plan does
     not occur in this branch. The bound keeps its `εaead` term, as ported.
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

  The premises and the bound are those of the ported statement. Used by `uakeInitiator_secure_dh`
  as hop 6. -/
lemma indistAdvantage_le_gap [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf εpk : ℝ)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      ((kdfPRFDH P).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    indistAdvantage P msg hasOPK A ≤
      q * (εgap + εaead + εkdf) + 2 * (q : ℝ) ^ 2 * εpk := by
  sorry

end Protocols.Models.PQXDH
