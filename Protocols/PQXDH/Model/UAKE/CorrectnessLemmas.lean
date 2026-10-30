/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.Defs

/-!
# Correctness Lemmas for the PQXDH model

Supporting lemmas for `Correctness.lean`: probability-to-support reductions,
round-trip facts for the abstract primitives, and characterizations of the
support of an honest protocol run. The proofs in this file are AI-written.

The hypothesis `hkem` (perfect KEM correctness) is an idealization. Production Kyber
decapsulates wrongly with a small probability, so the lemmas that assume it do not apply
to production Kyber.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

section CorrectnessLemmas

/-- Output probabilities under the `probComp` runtime's `evalDist` coincide
  with those of the computation itself. -/
lemma probOutput_probComp_evalDist {α : Type} (oa : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist oa] = Pr[= x | oa] := by
  rfl

/-- A Boolean computation that returns `true` with probability 1 has support
  `{true}`. -/
lemma support_eq_singleton_true_of_evalDist {oa : ProbComp Bool}
    (h : Pr[= true | ProbCompRuntime.probComp.evalDist oa] = 1) :
    support oa = {true} := by
  rw [probOutput_probComp_evalDist, probOutput_eq_one_iff] at h
  exact h.2

/-- Every key pair produced by `dhKeygen` satisfies `pk = sk • gen`. -/
lemma fst_eq_smul_of_mem_support_dhKeygen
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] {gen : G} {x : G × F}
    (hx : x ∈ support (dhKeygen (F := F) gen)) : x.1 = x.2 • gen := by
  simp only [dhKeygen, mem_support_bind_iff, mem_support_uniformSample, support_pure,
    Set.mem_singleton_iff, true_and] at hx
  obtain ⟨sk, rfl⟩ := hx
  rfl

/-- For a perfectly complete signature scheme, verifying an honestly generated
  signature can only return `true`. -/
lemma verify_eq_true_of_perfectlyComplete
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    {kp : SPK × SSK} (hkp : kp ∈ support P.sig.keygen)
    (m : G ⊕ PQPK) {σ : S} (hσ : σ ∈ support (P.sig.sign kp.1 kp.2 m))
    {b : Bool} (hb : b ∈ support (P.sig.verify kp.1 m σ)) : b = true := by
  have h := support_eq_singleton_true_of_evalDist (hsig m)
  have hmem : b ∈ support (do
      let (pk, sk) ← P.sig.keygen
      let s ← P.sig.sign pk sk m
      P.sig.verify pk m s) := by
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    exact (mem_support_bind_iff _ _ _).mpr ⟨σ, hσ, hb⟩
  rw [h] at hmem
  exact hmem

/-- For a perfectly correct KEM, decapsulating an honestly produced ciphertext
  can only return the encapsulated shared secret. Assumes perfect KEM correctness; see the
  module note. -/
lemma decaps_eq_some_of_perfectlyCorrect [DecidableEq SS]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    {kp : PQPK × PQSK} (hkp : kp ∈ support P.pqkem.keygen)
    {cs : CT × SS} (hcs : cs ∈ support (P.pqkem.encaps kp.1))
    {r : Option SS} (hr : r ∈ support (P.pqkem.decaps kp.2 cs.1)) : r = some cs.2 := by
  have h := support_eq_singleton_true_of_evalDist hkem
  have hmem : decide (r = some cs.2) ∈ support P.pqkem.CorrectExp := by
    unfold KEMScheme.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨cs, hcs, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨r, hr, ?_⟩
    simp
  rw [h] at hmem
  simpa using hmem

/-- For a perfectly correct AEAD, decryption inverts encryption under the same
  key and associated data. -/
lemma aead_decrypt_encrypt_of_perfectlyCorrect [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (k : K) (ad : G × G × PQPK) (m : Msg) {c : C}
    (hc : c ∈ support (P.aead.encrypt k ad m)) :
    P.aead.decrypt k ad c = some m := by
  have h := haead m ad
  rw [probOutput_eq_one_iff] at h
  have hmem : decide (P.aead.decrypt k ad c = some m) ∈
      support (AEAD.CorrectExp P.aead m ad) := by
    unfold AEAD.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨k, mem_support_uniformSample K, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨c, hc, ?_⟩
    simp
  rw [h.2] at hmem
  simpa using hmem

/-- Characterization of `initiate` on a pinned, correctly signed bundle: every
  outcome is `some`, built from an ephemeral key, an encapsulation, and an
  AEAD ciphertext drawn from the corresponding primitives' supports. -/
lemma mem_support_initiate
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    {p : InitiatorParameters F G SPK Msg} {bundle : PreKeyBundle G PQPK S IdC IdK}
    {r : Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)}
    (hpin : bundle.ikB = p.ikB)
    (hok₁ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB),
      b = true)
    (hok₂ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB),
      b = true)
    (hr : r ∈ support (initiate P p bundle)) :
    ∃ ekA ∈ support (dhKeygen (F := F) P.gen),
    ∃ cs ∈ support (P.pqkem.encaps bundle.pqpkB.1),
    ∃ ctxt ∈ support (P.aead.encrypt
        (P.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
          Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).2.1
        (p.ikA.1, p.ikB, bundle.pqpkB.1) p.msg),
      r = some (⟨p.ikA.1, ekA.1, cs.1, bundle.spkB.2, bundle.pqpkB.2,
          Option.map Prod.snd bundle.opkB, ctxt⟩,
        ⟨(P.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
            Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).1,
          (P.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
            Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).2.2,
          (p.ikA.1, p.ikB, bundle.pqpkB.1), p.msg⟩) := by
  simp only [initiate, hpin, ne_eq, not_true_eq_false, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, okSPK, hok, okPQPK, hok', hr⟩ := hr
  obtain rfl := hok₁ _ hok
  obtain rfl := hok₂ _ hok'
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := hr
  exact ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩

/-- DH agreement commutes on key pairs produced by `dhKeygen`. -/
lemma dh_comm [Field F] [AddCommGroup G] [Module F G] [SampleableType F] {gen : G}
    {x y : G × F} (hx : x ∈ support (dhKeygen (F := F) gen))
    (hy : y ∈ support (dhKeygen (F := F) gen)) : DH x.2 y.1 = DH y.2 x.1 := by
  rw [fst_eq_smul_of_mem_support_dhKeygen hx, fst_eq_smul_of_mem_support_dhKeygen hy,
    DH, DH, smul_smul, smul_smul, mul_comm]

/-- Characterization of `accept` when the key identifiers match,
  decapsulation yields `ss`, and Alice's ciphertext decrypts: the only outcome
  is the session context with the recomputed keys. -/
lemma mem_support_accept
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    {p : RecipientParameters F G PQPK PQSK SPK SSK S}
    {im : InitialMessage G CT C IdC IdK} {ss : SS} {m₀ : Msg}
    {r : Option (SessionContext G PQPK Msg K)}
    (hid₁ : im.idSPK = P.idEC p.spkB.1)
    (hid₂ : im.idPQPK = P.idKEM p.pqpkB.1)
    (hid₃ : im.idOPK = Option.map (fun opk => P.idEC opk.1) p.opkB)
    (hdec : ∀ o ∈ support (P.pqkem.decaps p.pqpkB.2 im.ct), o = some ss)
    (hdecr : P.aead.decrypt
        (P.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
          Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).2.1
        (im.ikA, p.ikB.1, p.pqpkB.1) im.ctxt = some m₀)
    (hr : r ∈ support (accept P p im)) :
    r = some ⟨(P.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).1,
      (P.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).2.2,
      (im.ikA, p.ikB.1, p.pqpkB.1), m₀⟩ := by
  simp only [accept, hid₁, hid₂, hid₃, ne_eq, not_true, or_self, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, o, ho, hr⟩ := hr
  obtain rfl := hdec _ ho
  simp only [hdecr, support_pure, Set.mem_singleton_iff] at hr
  exact hr

/-- Any key pair inside `genOPK`'s optional output is in the support of
  `dhKeygen`. -/
lemma opkB_mem_of_genOPK {F G : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    {gen : G} {hasOPK : Bool} {opkB : Option (G × F)}
    (h : opkB ∈ support (genOPK gen hasOPK)) :
    ∀ x ∈ opkB, x ∈ support (dhKeygen (F := F) gen) := by
  unfold genOPK at h
  cases hasOPK with
  | false =>
      simp only [Bool.false_eq_true, if_false, support_pure, Set.mem_singleton_iff] at h
      subst h; simp
  | true =>
      simp only [if_true, support_map, Set.mem_image] at h
      obtain ⟨opk, hopk, rfl⟩ := h
      intro x hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ hopk

/-- Support characterization of an honest run of the T=Bob scheme: under the
  correctness hypotheses, both parties output `some` of the same key, and the
  transcript carries exactly the scheme's 3 messages. Assumes perfect KEM correctness; see
  the module note. -/
lemma run_support_initiator
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (msg : Msg)
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.1)))
    {uOut tOut : Option (Option K)} {ms : List (Message G PQPK CT S C IdC IdK)}
    (hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (initiator P) (recipient P hasOPK)
      ⟨ikA, ikB.1, sigkB.1, msg⟩ ⟨ikB, sigkB, spkB, spkSigB⟩ (3 + 1))) :
    (∃ k, uOut = some (some k) ∧ tOut = some (some k)) ∧ ms.length = 3 := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, rfl, qInit,
    ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.runHonestStart, Party.InitResult.opening,
    Party.InitResult.state] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  obtain ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := mem_support_initiate P rfl
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir
  simp only [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  dsimp only at hctxt hcs hy
  have hmap : Option.map (fun opk => DH ekA.2 opk.1)
      (Option.map (fun opk => (opk.1, P.idEC opk.1)) opkB)
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB <;> rfl
  have hdh1 : DH spkB.2 ikA.1 = DH ikA.2 spkB.1 := dh_comm hspkB hikA
  have hdh2 : DH ikB.2 ekA.1 = DH ekA.2 ikB.1 := dh_comm hikB hekA
  have hdh3 : DH spkB.2 ekA.1 = DH ekA.2 spkB.1 := dh_comm hspkB hekA
  have hdh4 : Option.map (fun opk => DH opk.2 ekA.1) opkB
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB with
    | none => rfl
    | some opk =>
        simp only [Option.map_some]
        rw [dh_comm (hopkB opk rfl) hekA]
  rw [hmap] at hctxt hy
  have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
  simp only [Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hy
  obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
  have hbob := mem_support_accept P rfl rfl (by cases opkB <;> rfl)
    (fun o ho => decaps_eq_some_of_perfectlyCorrect P hkem hpqpkB hcs ho)
    (by dsimp only; rw [hdh1, hdh2, hdh3, hdh4]; exact hdecA) har
  subst hbob
  dsimp only at hsr
  rw [hdh1, hdh2, hdh3, hdh4] at hsr
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
  obtain ⟨conf, hconf, rfl⟩ := hsr
  have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
  simp only [confirm, hconfirm, mem_support_bind_iff] at hy
  simp only [if_true, support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨x, rfl, hy⟩ := hy
  simp only [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
  obtain ⟨x, rfl, x1, rfl, h1, h2, hms⟩ := hout
  exact ⟨⟨_, h1, h2⟩, by simp [hms]⟩

/-- Support characterization of an honest run of the T=Alice scheme: under the
  correctness hypotheses, both parties output `some` of the same key, and the
  transcript carries exactly the scheme's 2 messages. Assumes perfect KEM correctness; see
  the module note. -/
lemma run_support_recipient
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (msg : Msg)
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.1)))
    {uOut tOut : Option (Option K)} {ms : List (Message G PQPK CT S C IdC IdK)}
    (hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (recipientNoConfirm P hasOPK)
      (initiatorNoConfirm P) ⟨ikB, sigkB, spkB, spkSigB⟩ ⟨ikA, ikB.1, sigkB.1, msg⟩ (2 + 1))) :
    (∃ k, uOut = some (some k) ∧ tOut = some (some k)) ∧ ms.length = 2 := by
  simp only [Party.runHonest, initiatorNoConfirm, recipientNoConfirm, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hrun
  obtain ⟨pInit,
    ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, qInit, rfl, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.runHonestStart, Party.InitResult.opening,
    Party.InitResult.state] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  obtain ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := mem_support_initiate P rfl
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
    (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir
  simp only [support_pure, Set.mem_singleton_iff] at hr
  subst hr
  dsimp only at hctxt hcs hy
  have hmap : Option.map (fun opk => DH ekA.2 opk.1)
      (Option.map (fun opk => (opk.1, P.idEC opk.1)) opkB)
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB <;> rfl
  have hdh1 : DH spkB.2 ikA.1 = DH ikA.2 spkB.1 := dh_comm hspkB hikA
  have hdh2 : DH ikB.2 ekA.1 = DH ekA.2 ikB.1 := dh_comm hikB hekA
  have hdh3 : DH spkB.2 ekA.1 = DH ekA.2 spkB.1 := dh_comm hspkB hekA
  have hdh4 : Option.map (fun opk => DH opk.2 ekA.1) opkB
      = Option.map (fun opk => DH ekA.2 opk.1) opkB := by
    cases opkB with
    | none => rfl
    | some opk =>
        simp only [Option.map_some]
        rw [dh_comm (hopkB opk rfl) hekA]
  rw [hmap] at hctxt hy
  have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
  simp only [Bool.false_eq_true, ↓reduceIte, mem_support_bind_iff] at hy
  obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
  have hbob := mem_support_accept P rfl rfl (by cases opkB <;> rfl)
    (fun o ho => decaps_eq_some_of_perfectlyCorrect P hkem hpqpkB hcs ho)
    (by dsimp only; rw [hdh1, hdh2, hdh3, hdh4]; exact hdecA) har
  subst hbob
  dsimp only at hsr
  rw [hdh1, hdh2, hdh3, hdh4] at hsr
  simp only [support_pure, Set.mem_singleton_iff] at hsr
  subst hsr
  simp only [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
  obtain ⟨x, rfl, x1, rfl, h1, h2, hms⟩ := hout
  exact ⟨⟨_, h1, h2⟩, by simp [hms]⟩

end CorrectnessLemmas

end Protocols.PQXDH
