/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.Models.PQXDH.UAKE.CorrectnessLemmas
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Partnering

/-!
# Original-key partnering of the PQXDH model

Alice's challenge session and a session of Bob are partners when both have accepted with the same
associated data `ad` and the same key material `km`, the input of `P.kdf`. Each party keeps its
session context, which stores `km`, once it accepts, so the session identifier `(ad, km)` exists
exactly on the accepted states. Equal inputs give equal keys, since `P.kdf` is a function, but
distinct inputs that give equal keys do not make partners. The key identifiers, the signatures and
the bytes of an unsigned one-time pre-key are not part of the identifier, so they are not
authenticated. `originalKeyPartnering` is the partnering of `uakeInitiator` that the security
theorems use with `PartneredExp`. `initiate_km_spec` and `accept_km_spec` show that the stored
`km` is the input of the KDF call that derives the session's keys.

The definitions and proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace Protocols.Models.PQXDH

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}

/-- The session identifier of Alice's state: her associated data and key material, once she has
accepted Bob's confirmation. Earlier states have none. -/
def initiatorSid :
    InitiatorParameters F G Msg ⊕ SessionContext G PQPK Msg K SS ⊕
        SessionContext G PQPK Msg K SS →
      Option ((G × G × PQPK) × KeyMaterial G SS)
  | .inr (.inr ctx) => some (ctx.ad, ctx.km)
  | _ => none

/-- The session identifier of Bob's state: his associated data and key material, once he has
accepted Alice's initial message. Earlier states have none. -/
def recipientSid :
    RecipientParameters F G PQPK PQSK S ⊕ SessionContext G PQPK Msg K SS →
      Option ((G × G × PQPK) × KeyMaterial G SS)
  | .inl _ => none
  | .inr ctx => some (ctx.ad, ctx.km)

/-- Original-key partnering for `uakeInitiator`: Alice's state and Bob's state are partners when
both have accepted with the same associated data and the same key material. -/
def originalKeyPartnering [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    Partnering (uakeInitiator P msg hasOPK) where
  partner sa sb := ∃ s, initiatorSid sa = some s ∧ recipientSid sb = some s

/-- Two states are original-key partners exactly when both are accepted and their contexts agree
on the associated data and the key material. -/
theorem originalKeyPartnering_partner_iff [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (sa : (uakeInitiator P msg hasOPK).U.State) (sb : (uakeInitiator P msg hasOPK).T.State) :
    (originalKeyPartnering P msg hasOPK).partner sa sb ↔
      ∃ ca cb : SessionContext G PQPK Msg K SS,
        sa = Sum.inr (Sum.inr ca) ∧ sb = Sum.inr cb ∧ ca.ad = cb.ad ∧ ca.km = cb.km := by
  change (∃ s, initiatorSid sa = some s ∧ recipientSid sb = some s) ↔ _
  constructor
  · rintro ⟨s, hA, hB⟩
    rcases sa with p | ca | ca <;> rcases sb with q | cb <;>
      simp only [initiatorSid, recipientSid, reduceCtorEq] at hA hB
    rw [← hB, Option.some.injEq, Prod.mk.injEq] at hA
    exact ⟨ca, cb, rfl, rfl, hA.1, hA.2⟩
  · rintro ⟨ca, cb, rfl, rfl, h1, h2⟩
    exact ⟨(ca.ad, ca.km), rfl, by simp only [recipientSid, h1, h2]⟩

/-- On every outcome of `initiate`, the context holds the protocol's associated data, the keys
`sk` and `kb` derived from `km`, and the key material computed from Alice's keys, a fresh
ephemeral key and an encapsulation to the bundle's KEM key. -/
theorem initiate_km_spec [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK)
    {p : InitiatorParameters F G Msg} {bundle : PreKeyBundle G PQPK S IdC IdK}
    {im : InitialMessage G CT C IdC IdK} {ctx : SessionContext G PQPK Msg K SS}
    (h : some (im, ctx) ∈ support (initiate P p bundle)) :
    ctx.ad = (p.ikA.1, bundle.ikB, bundle.pqpkB.1) ∧
      ctx.sk = (P.kdf ctx.km).1 ∧ ctx.kb = (P.kdf ctx.km).2.2 ∧
      ∃ ekA ∈ support (dhKeygen (F := F) P.gen),
        ∃ cs ∈ support (P.pqkem.encaps bundle.pqpkB.1),
          im.ekA = ekA.1 ∧ im.ct = cs.1 ∧
          ctx.km = (DH p.ikA.2 bundle.spkB.1, DH ekA.2 bundle.ikB, DH ekA.2 bundle.spkB.1,
            bundle.opkB.map (fun opk => DH ekA.2 opk.1), cs.2) := by
  unfold initiate at h
  split_ifs at h with hpin
  · simp at h
  · simp only [mem_support_bind_iff] at h
    obtain ⟨okSPK, -, okPQPK, -, h⟩ := h
    split_ifs at h with hok
    · simp at h
    · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
      obtain ⟨ekA, hekA, cs, hcs, ctxt, -, h⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, ekA, hekA, cs, hcs, rfl, rfl, rfl⟩

/-- On every outcome of `accept`, the context holds the protocol's associated data, the keys `sk`
and `kb` derived from `km`, and the key material computed from Bob's keys, the message and a
decapsulation of its ciphertext. -/
theorem accept_km_spec [Field F] [AddCommGroup G] [Module F G] [DecidableEq IdC]
    [DecidableEq IdK] (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK)
    {p : RecipientParameters F G PQPK PQSK S} {im : InitialMessage G CT C IdC IdK}
    {ctx : SessionContext G PQPK Msg K SS} (h : some ctx ∈ support (accept P p im)) :
    ctx.ad = (im.ikA, p.ikB.1, p.pqpkB.1) ∧
      ctx.sk = (P.kdf ctx.km).1 ∧ ctx.kb = (P.kdf ctx.km).2.2 ∧
      ∃ ss, some ss ∈ support (P.pqkem.decaps p.pqpkB.2 im.ct) ∧
        ctx.km = (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
          p.opkB.map (fun opk => DH opk.2 im.ekA), ss) := by
  unfold accept at h
  split_ifs at h with hid
  · simp at h
  · simp only [mem_support_bind_iff] at h
    obtain ⟨o, ho, h⟩ := h
    rcases o with _ | ss
    · simp at h
    · simp only at h
      split at h
      · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl, ss, ho, rfl⟩
      · simp at h

end Protocols.Models.PQXDH
