/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.SecurityLemmas.Games
import Protocols.ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# GapDH Core Hops

Hops 5 and 6 of the DH security theorem `Protocols.PQXDH.uakeInitiator_secure_dh` in
`Security.lean`: the forgery and indistinguishability cores, against GapDH,
the KDF, and the AEAD. See `SecurityLemmas.lean` for the overall map.

These statements are believed true in the current model (the KDF as a plain
parameter function, plus a PRF hypothesis), but the standard reductions
require the KDF to be a programmable random oracle, so their proofs are
deferred to that planned model change; the intended sub-hops are recorded
in the doc comments.

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

/-- Hop 5 (forgery core, GapDH): with an honest bundle and separated KEM
  keys, a forgery requires breaking GapDH, the KDF, or the AEAD.

  Intended proof, as further hops once the KDF is modeled as a random oracle
  (see the module comment):
  1. Identify the unique T-oracle session that can share the challenge
     session's key material: the accepted bundle pins `ikB` (checked by the
     initiator), `spkB` (the only EC key `setup` signs), and `pqpkB`
     (published by exactly one session, by `hidKEM` and the excluded
     collision event).
  2. Replace the KDF output triple `(SK, KA, KB)` on the challenge session's
     key material with a fresh uniform triple, shared with any T-oracle
     session that derives identical key material. A distinguisher must query
     the KDF on the challenge key material, whose third DH component is
     `DH ekA.2 spkB.1` for the challenge session's fresh ephemeral `ekA`;
     embedding the GapDH challenge in `ekA` and `spkB`, recognizing the
     query with the DDH oracle, and answering the T oracle's other KDF
     queries consistently (again via the DDH oracle) yields a GapDH
     adversary. This step consumes `εgap` and, under the current PRF
     modeling of the KDF, `εkdf`.
  3. With `KA` uniform, an initial message accepted by the paired session
     with a modified AEAD ciphertext is a forgery against `KA` (first
     `εaead`, via the INT-CTXT-D game whose encryption oracle produces the
     challenge session's ciphertext).
  4. With `KB` uniform, the confirmation the initiator accepts must have
     been produced under `KB` by the paired session (second `εaead`); a
     verbatim relay of honestly produced messages forces the global-clock
     interleaving of `Matching`, so the transcripts match, contradicting
     the forgery event.

  The factor `q` is generous (the reduction handles all sessions at once),
  but stating the bound with it makes the composed bound collapse to `εsig`
  when the adversary opens no sessions, in which case completing the
  challenge session already requires a signature forgery.

  Used by `uakeInitiator_secure_dh` as hop 5. A proof would follow the steps above once the KDF
  model is ruled, but the last step does not hold as stated, since unsigned bundle fields (the
  key identifiers and the one-time pre-key) can change without changing the derived keys, so the
  transcripts differ with no forgery.

  The premise `hidKEM` does not hold for production, where key identifiers are 32-bit
  prekey ids and no map from KEM public keys to them is injective. It is kept until it is
  removed with the restatement of this hop. Issue #35 reports the underlying problem:
  unsigned key identifiers break transcript matching. -/
lemma forgeHonestGoodProb_le_gap [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf : ℝ)
    (hidKEM : Function.Injective P.idKEM)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    forgeHonestGoodProb P msg hasOPK A ≤ q * (εgap + 2 * εaead + εkdf) := by
  sorry

/-- Hop 6 (indistinguishability core, GapDH): in `indistExp`, the
  adversary's guess is better than a fair coin only by breaking GapDH, the
  KDF, or the AEAD, or by a KEM public-key collision.

  Intended proof, as further hops once the KDF is modeled as a random oracle
  (see the module comment):
  1. If the challenge session outputs no key, both finalizations hand the
     adversary `none` and the guess is independent of the challenge bit, so
     it wins with probability exactly `1 / 2`; the coined forgery branch
     likewise. Only the ping-pong branch remains.
  2. In the ping-pong branch, the accepted bundle equals a T-oracle
     session's published bundle (their transcripts match message by
     message), so the bundle is honest without a signature hypothesis.
  3. Replace the KDF output triple on the challenge session's key material
     with a fresh uniform triple, as in the forgery core (`εgap` plus, under
     the current PRF modeling, `εkdf`).
  4. If the matching session derived different key material (a KEM
     decapsulation mismatch), the confirmation the initiator accepted
     decrypts under the now-uniform `KB` without having been produced under
     it: an AEAD forgery (`εaead`).
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

  Used by `uakeInitiator_secure_dh` as hop 6. A proof would follow the steps above once the KDF
  model is ruled.

  The premise `hidKEM` does not hold for production, where key identifiers are 32-bit
  prekey ids and no map from KEM public keys to them is injective. It is kept until it is
  removed with the restatement of this hop. Issue #35 reports the underlying problem:
  unsigned key identifiers break transcript matching. -/
lemma indistAdvantage_le_gap [DecidableEq SS] [Fintype K] [Inhabited K]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εgap εaead εkdf εpk : ℝ)
    (hidKEM : Function.Injective P.idKEM)
    (hgap : ∀ D : DiffieHellman.GapDHAdversary F G,
      DiffieHellman.gapDHAdvantage P.gen D ≤ εgap)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf)
    (hpk : ∀ pk : PQPK, (Pr[= pk | Prod.fst <$> P.pqkem.keygen]).toReal ≤ εpk) :
    indistAdvantage P msg hasOPK A ≤
      q * (εgap + εaead + εkdf) + 2 * (q : ℝ) ^ 2 * εpk := by
  sorry

end Protocols.PQXDH
