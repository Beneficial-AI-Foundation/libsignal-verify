/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Protocol.Kem.Ciphertext
import Protocols.PQXDH.AcceptBranches
import Protocols.PQXDH.InitiateBranches
import Protocols.PQXDH.Kdf
import Protocols.PQXDH.Scheme

/-!
# One honest run of the extracted entry points

In one honest run on valid key pairs, both extracted entry points of the handshake return their
keys, and the keys agree when the Kyber secrets agree. `honest_run_ok` states this with the
parameter records that `coreHonestRun` builds.
-/

open OracleSpec OracleComp
open Aeneas Aeneas.Std Result
open libsignal_protocol

namespace Protocols.PQXDH

/-- Under the backend contract `KyberEncapsBackend`, on a 1568-byte key and a generator state in
`Dom`, the extracted encapsulation returns a 32-byte shared secret `ss` and the serialized
ciphertext `ct`, which is the key-type byte `8` followed by the 1568 bytes `ct0` of the backend's
ciphertext (`rust/protocol/src/kem.rs:363-385`). -/
theorem encapsulate_ok (hE : KyberEncapsBackend) {R : Type} (crng : rand_core_1.CryptoRng R)
    (Dom : R → Prop) (hRng : RngTotal crng.RngCoreInst Dom) (pk : PQPub) (r : R)
    (hpk : pk.key_data.data.length = 1568) (hr : Dom r) :
    ∃ (ss ct0 ct : Slice U8) (r' : R),
      kem.KeyPublic.encapsulate crng pk r = .ok (.Ok (ss, ct), r') ∧ ss.length = 32 ∧
        ct0.length = 1568 ∧ ct.val = 8#u8 :: ct0.val := by
  obtain ⟨⟨res, r1⟩, hb, hpost⟩ := exists_ok_of_spec (hE crng Dom hRng pk.key_data r hpk hr)
  simp only [WP.uncurry'] at hpost
  obtain ⟨⟨ss, ct0, rfl, hss, hct0⟩, -⟩ := hpost
  have hlt : ct0.length < Usize.max := by
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max, U64.max] <;> scalar_tac
  obtain ⟨ct, hser, hctv⟩ :=
    exists_ok_of_spec (kem.Ciphertext.serialize_spec { key_type := pk.key_type, data := ct0 } hlt)
  refine ⟨ss, ct0, ct, r1, ?_, hss, hct0, hctv⟩
  unfold kem.KeyPublic.encapsulate
  simp [hb, hser, core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch]

/-- Under the contract `KyberDecaps`, on a 3168-byte secret key, the extracted decapsulation of
the bytes `8` followed by 1568 bytes `ct0` returns a 32-byte shared secret
(`rust/protocol/src/kem.rs:391-415`). The secret need not equal any encapsulated one. -/
theorem decapsulate_serialized_ok (hD : KyberDecaps) (sk : PQPriv) (ct ct0 : Slice U8)
    (hsk : sk.key_data.data.length = 3168) (hct : ct.val = 8#u8 :: ct0.val)
    (hct0 : ct0.length = 1568) :
    ∃ ss : Slice U8, kem.KeySecret.decapsulate sk ct = .ok (.Ok ss) ∧ ss.length = 32 := by
  obtain ⟨r, hdes, hr⟩ := exists_ok_of_spec (kem.Ciphertext.deserialize_spec ct ct0 hct hct0)
  subst hr
  obtain ⟨r1, hr1, hpost⟩ := exists_ok_of_spec (hD sk.key_data ct0)
  obtain ⟨ss, rfl, hss⟩ := hpost.2.2 hsk hct0
  refine ⟨ss, ?_, hss⟩
  have hne : core.cmp.PartialEq.ne.trait_default kem.KeyType.Insts.CoreCmpPartialEqKeyType
      kem.KeyType.Kyber1024 sk.key_type = ok false := by
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      kem.KeyType.Insts.CoreCmpPartialEqKeyType.eq]
  unfold kem.KeySecret.decapsulate
  simp [hdes, hne, hr1, core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch]

/-- For two valid curve25519 key pairs, the agreement of the first private key with the second
public key and the agreement of the second private key with the first public key return the same
32 bytes. This is `AgreementDerived` on key pairs. -/
theorem agreement_of_valid (hA : AgreementDerived) {kp₁ kp₂ : ECKeyPair}
    (h₁ : ECKeyPairValid kp₁) (h₂ : ECKeyPairValid kp₂) :
    ∃ s : Slice U8, s.length = 32 ∧
      curve.PrivateKey.calculate_agreement kp₁.private_key kp₂.public_key = .ok (.Ok s) ∧
      curve.PrivateKey.calculate_agreement kp₂.private_key kp₁.public_key = .ok (.Ok s) :=
  hA kp₁.private_key kp₂.private_key kp₁.public_key kp₂.public_key h₁ h₂

/-- On 32-byte agreement values and a 32-byte Kyber secret, `kdfInput` returns some key material
`km`, and the extracted key derivation on `km` returns keys whose chain index is `0`. -/
theorem kdfInput_derive_ok (H : crypto.HmacSha256) (hH : crypto.HkdfSha256Contract H)
    (d1 d2 d3 ss : Slice U8) (d4 : Option (Slice U8)) (h1 : d1.length = 32)
    (h2 : d2.length = 32) (h3 : d3.length = 32) (h4 : ∀ d ∈ d4, d.length = 32)
    (hss : ss.length = 32) :
    ∃ (km : Slice U8) (hk : HandshakeKeys), kdfInput d1 d2 d3 d4 ss = .ok km ∧
      pqxdh.HandshakeKeys.derive km = .ok hk ∧ hk.chain_key.index = 0#u32 := by
  have h192 : 192 ≤ Usize.max := by
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max, U64.max] <;> scalar_tac
  have e1 : d1.val.length = 32 := h1
  have e2 : d2.val.length = 32 := h2
  have e3 : d3.val.length = 32 := h3
  have es : ss.val.length = 32 := hss
  have hlen : (kdfInputSliceBytes d1 d2 d3 d4 ss).length ≤ Usize.max := by
    rcases d4 with _ | d
    · simp only [kdfInputSliceBytes, List.length_append, List.length_replicate, e1, e2, e3, es,
        List.length_nil]
      omega
    · have e4 : d.val.length = 32 := h4 d rfl
      simp only [kdfInputSliceBytes, List.length_append, List.length_replicate, e1, e2, e3, es,
        e4]
      omega
  obtain ⟨km, hkm, -⟩ := exists_ok_of_spec (kdfInput_spec d1 d2 d3 d4 ss hlen)
  obtain ⟨hk, hder, hpost⟩ := exists_ok_of_spec (pqxdh.HandshakeKeys.derive_spec H hH km)
  exact ⟨km, hk, hkm, hder, hpost.2.2.1⟩

/-- If every key pair from `P.ecKeygen` is valid, every key pair in a possible output of
`genOPK P hasOPK` is valid. -/
theorem genOPK_valid {Rand Msg C IdC IdK : Type} (P : Params Rand Msg C IdC IdK)
    (hasOPK : Bool) (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp) :
    ∀ o ∈ support (genOPK P hasOPK), ∀ kp ∈ o, ECKeyPairValid kp := by
  intro o ho kp hkp
  cases hasOPK
  · simp only [genOPK, Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at ho
    subst ho
    simp at hkp
  · simp only [genOPK, ite_true, support_map] at ho
    obtain ⟨kp', hkp', rfl⟩ := ho
    have : kp = kp' := by simpa using hkp.symm
    exact this ▸ hEC kp' hkp'

/-- One honest run of the extracted entry points. Suppose that the curve25519 key pairs are
valid, that Bob's Kyber key pair has the Kyber1024 shape, and that the generator state `r` is in
`Dom`. Then the encapsulation to Bob's Kyber key returns a secret `ss`, a ciphertext `ct` and a
state `r'`, and the decapsulation of `ct` returns a secret `ss'`. `pqxdh_initiate` returns its
keys `hkA` with `ct` and `r'`, and `pqxdh_accept` on `ct` returns its keys `hkB`. The chain index
of `hkB` is `0`, and the two keys are equal when the two secrets are equal. -/
theorem honest_run_ok (hC : CoreContracts) (H : crypto.HmacSha256)
    (hH : crypto.HkdfSha256Contract H) {Rand : Type} (rng : rand.rng.Rng Rand)
    (crng : rand_core_1.CryptoRng Rand) (Dom : Rand → Prop)
    (hRng : RngTotal crng.RngCoreInst Dom) (ikA ikB spkB ekA : ECKeyPair)
    (opkB : Option ECKeyPair) (pqpkB : PQKeyPair) (r : Rand)
    (hikA : ECKeyPairValid ikA) (hikB : ECKeyPairValid ikB) (hspkB : ECKeyPairValid spkB)
    (hekA : ECKeyPairValid ekA) (hopkB : ∀ kp ∈ opkB, ECKeyPairValid kp)
    (hpq : PQKeyPairShape pqpkB) (hr : Dom r) :
    ∃ (ss ct ss' : Slice U8) (r' : Rand) (hkA hkB : HandshakeKeys),
      kem.KeyPublic.encapsulate crng pqpkB.public_key r = .ok (.Ok (ss, ct), r') ∧
      kem.KeySecret.decapsulate pqpkB.secret_key ct = .ok (.Ok ss') ∧
      pqxdh.pqxdh_initiate rng crng
          { our_identity_key_pair := identityKeyPairOf ikA
            our_ephemeral_key_pair := ekA
            their_identity_key := identityKeyOf ikB
            their_signed_pre_key := spkB.public_key
            their_one_time_pre_key := opkB.map (·.public_key)
            their_ratchet_key := spkB.public_key
            their_kyber_pre_key := pqpkB.public_key
            self_session := false } r =
        .ok (.Ok { keys := hkA, kyber_ciphertext := ct }, r') ∧
      pqxdh.pqxdh_accept
          { our_identity_key_pair := identityKeyPairOf ikB
            our_signed_pre_key_pair := spkB
            our_one_time_pre_key_pair := opkB
            our_kyber_pre_key_pair := pqpkB
            their_identity_key := identityKeyOf ikA
            their_ephemeral_key := ekA.public_key
            their_kyber_ciphertext := ct
            self_session := false } = .ok (.Ok hkB) ∧
      hkB.chain_key.index = 0#u32 ∧ (ss' = ss → hkA = hkB) := by
  obtain ⟨-, -, hpkL, hskL⟩ := hpq
  obtain ⟨d1, hd1l, hI1, hR1⟩ := agreement_of_valid hC.agreementDerived hikA hspkB
  obtain ⟨d2, hd2l, hI2, hR2⟩ := agreement_of_valid hC.agreementDerived hekA hikB
  obtain ⟨d3, hd3l, hI3, hR3⟩ := agreement_of_valid hC.agreementDerived hekA hspkB
  obtain ⟨d4, hd4l, hI4, hR4⟩ : ∃ d4 : Option (Slice U8), (∀ d ∈ d4, d.length = 32) ∧
      (match opkB with
        | none => d4 = none
        | some opk => ∃ d, curve.PrivateKey.calculate_agreement ekA.private_key opk.public_key =
            .ok (.Ok d) ∧ d4 = some d) ∧
      (match opkB with
        | none => d4 = none
        | some opk => ∃ d, curve.PrivateKey.calculate_agreement opk.private_key ekA.public_key =
            .ok (.Ok d) ∧ d4 = some d) := by
    rcases opkB with _ | opk
    · exact ⟨none, by simp, rfl, rfl⟩
    · obtain ⟨s, hs, h1, h2⟩ := agreement_of_valid hC.agreementDerived hekA (hopkB opk rfl)
      refine ⟨some s, ?_, ⟨s, h1, rfl⟩, ⟨s, h2, rfl⟩⟩
      intro d hd
      simp only [Option.mem_def, Option.some.injEq] at hd
      subst hd
      exact hs
  obtain ⟨ss, ct0, ct, r', henc, hss, hct0, hct⟩ :=
    encapsulate_ok hC.kyberEncapsBackend crng Dom hRng pqpkB.public_key r hpkL hr
  obtain ⟨ss', hdec, hss'⟩ :=
    decapsulate_serialized_ok hC.kyberDecaps pqpkB.secret_key ct ct0 hskL hct hct0
  obtain ⟨kmA, hkA, hkmA, hderA, -⟩ :=
    kdfInput_derive_ok H hH d1 d2 d3 ss d4 hd1l hd2l hd3l hd4l hss
  obtain ⟨kmB, hkB, hkmB, hderB, hidxB⟩ :=
    kdfInput_derive_ok H hH d1 d2 d3 ss' d4 hd1l hd2l hd3l hd4l hss'
  refine ⟨ss, ct, ss', r', hkA, hkB, henc, hdec, ?_, ?_, hidxB, ?_⟩
  · refine initiate_ok_eq crng rng _ r r' d1 d2 d3 ss ct kmA d4 hkA ?_ henc hkmA hderA
    refine ⟨hI1, hI2, hI3, ?_⟩
    rcases opkB with _ | opk
    · exact hI4
    · exact hI4
  · refine accept_ok_eq _ d1 d2 d3 ss' kmB d4 hkB
      (hC.derivedCanonical ekA.private_key ekA.public_key hekA) ?_ hdec hkmB hderB
    refine ⟨hR1, hR2, hR3, ?_⟩
    rcases opkB with _ | opk
    · exact hR4
    · exact hR4
  · intro h
    subst h
    rw [hkmA] at hkmB
    simp only [Result.ok.injEq] at hkmB
    subst hkmB
    rw [hderA] at hderB
    simpa only [Result.ok.injEq] using hderB

end Protocols.PQXDH
