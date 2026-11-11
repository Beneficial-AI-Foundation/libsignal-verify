/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.PQXDH.Correctness
import Protocols.PQXDH.Kdf
import Protocols.PQXDH.Security
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.DistAdvantage

/-!
# Spec summary: the Full realization of PQXDH

This file freezes the headline statements of the Full realization. Each theorem is restated with
`recall`, which checks that the restatement is definitionally equal to the declared statement.
Each theorem and central definition also has a `#guard_msgs` check on the constants it depends
on. The build fails if a statement or its trust changes. A reader can check the statements here,
together with the definitions they mention, without reading the proofs.

The dependencies of a statement are the opaque leaves of the extracted code that its definitions
mention (for example `curve.PrivateKey.calculate_agreement`), the native-decision constant that
the extraction of `pqxdh_accept` introduces, and the stub marker when the proof, or a proof it
uses, is a stub. `Protocols/LEDGER.md` lists the stubs apart from the admitted hops of the
abstract model, in two groups: temporary stubs of the correctness statements and their supporting
lemmas, and security placeholders for the security statements and `fullExp_noLostMass`.

The fault fixtures, which show that the correctness statements are not vacuous, are in
`ProtocolsTest/PQXDH/FaultFixtures.lean` and carry their own dependency checks.
-/

open Protocols.PQXDH Protocols.Realization

/-! ## Security -/

/-! Each headline bound carries its fault term `Pr[⊥]`. Below it, the file recalls the bound
without that term, with the totality premises that it adds. -/

recall Protocols.PQXDH.uakeInitiator_secure_dh
    {Rand Msg C IdC IdK : Type} [DecidableEq Msg] [DecidableEq C] [DecidableEq IdC]
    [DecidableEq IdK] (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (H : libsignal_protocol.crypto.HmacSha256) (hC : PartialContracts H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (A : AKE.UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK)) (q : ℕ)
    (hq : A.OpensAtMostPerPhase q) (εsig εodh εaead εpk : ℝ)
    (hsig : ∀ (B : JointSigAdversary), (jointSigAdvantage P B).toReal ≤ εsig)
    (hodh : ∀ (D : PqxdhODHAdversary), pqxdhODHAdvantage H P D ≤ εodh)
    (haead : ∀ (B : AEAD.INT_CTXT_D_Adversary P.aead), AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hpk : ∀ (pk : PQPub),
      (Pr{let y ← (fun x => x.public_key) <$> P.pqKeygen}[y = pk]).toReal ≤ εpk)
    : fullAdvantage P msg hasOPK A ≤ εsig + 2 * ↑q * (εodh + 2 * εaead) + 3 * ↑q ^ 2 * εpk
      + (rustRuntime.prFail (fullExp P msg hasOPK A)).toReal

/--
info: 'Protocols.PQXDH.uakeInitiator_secure_dh' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.uakeInitiator_secure_dh

recall Protocols.PQXDH.uakeInitiator_secure_dh_total
    {Rand Msg C IdC IdK : Type} [DecidableEq Msg] [DecidableEq C] [DecidableEq IdC]
    [DecidableEq IdK] (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (H : libsignal_protocol.crypto.HmacSha256) (hC : PartialContracts H) (hCt : CoreContracts)
    (hS : SignatureContracts) (hH : libsignal_protocol.crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r)
    (A : AKE.UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK))
    (hA : Adversary.SendsFittingMessages A) (q : ℕ) (hq : A.OpensAtMostPerPhase q)
    (εsig εodh εaead εpk : ℝ)
    (hsig : ∀ (B : JointSigAdversary), (jointSigAdvantage P B).toReal ≤ εsig)
    (hodh : ∀ (D : PqxdhODHAdversary), pqxdhODHAdvantage H P D ≤ εodh)
    (haead : ∀ (B : AEAD.INT_CTXT_D_Adversary P.aead), AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hpk : ∀ (pk : PQPub),
      (Pr{let y ← (fun x => x.public_key) <$> P.pqKeygen}[y = pk]).toReal ≤ εpk)
    : fullAdvantage P msg hasOPK A ≤ εsig + 2 * ↑q * (εodh + 2 * εaead) + 3 * ↑q ^ 2 * εpk

/--
info: 'Protocols.PQXDH.uakeInitiator_secure_dh_total' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.uakeInitiator_secure_dh_total

recall Protocols.PQXDH.uakeInitiator_secure_pq
    {Rand Msg C IdC IdK : Type} [DecidableEq Msg] [DecidableEq C] [DecidableEq IdC]
    [DecidableEq IdK] (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (H : libsignal_protocol.crypto.HmacSha256) (hC : PartialContracts H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
    (K : KEMScheme ProbComp Key PQPub PQPriv (Aeneas.Std.Slice Aeneas.Std.U8))
    (hK : KyberBridge P K)
    (A : AKE.UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK)) (q : ℕ)
    (hq : A.OpensAtMostPerPhase q) (εsig εkem εaead εkdf εpk : ℝ)
    (hsig : ∀ (B : JointSigAdversary), (jointSigAdvantage P B).toReal ≤ εsig)
    (hkem : ∀ (B : K.IND_CCA_Adversary),
      (KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    (haead : ∀ (B : AEAD.INT_CTXT_D_Adversary P.aead), AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (D : PRFScheme.PRFAdversary (Key × Key × Key × Option Key) (Key × Key × Key)),
      ((kdfPRF H).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ (pk : PQPub),
      (Pr{let y ← (fun x => x.public_key) <$> P.pqKeygen}[y = pk]).toReal ≤ εpk)
    : fullAdvantage P msg hasOPK A ≤ εsig + 2 * ↑q * (εkem + εaead + εkdf) + 3 * ↑q ^ 2 * εpk
      + (rustRuntime.prFail (fullExp P msg hasOPK A)).toReal

/--
info: 'Protocols.PQXDH.uakeInitiator_secure_pq' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.uakeInitiator_secure_pq

recall Protocols.PQXDH.uakeInitiator_secure_pq_total
    {Rand Msg C IdC IdK : Type} [DecidableEq Msg] [DecidableEq C] [DecidableEq IdC]
    [DecidableEq IdK] (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool)
    (H : libsignal_protocol.crypto.HmacSha256) (hC : PartialContracts H) (hCt : CoreContracts)
    (hS : SignatureContracts) (hH : libsignal_protocol.crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r)
    (K : KEMScheme ProbComp Key PQPub PQPriv (Aeneas.Std.Slice Aeneas.Std.U8))
    (hK : KyberBridge P K)
    (A : AKE.UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK))
    (hA : Adversary.SendsFittingMessages A) (q : ℕ) (hq : A.OpensAtMostPerPhase q)
    (εsig εkem εaead εkdf εpk : ℝ)
    (hsig : ∀ (B : JointSigAdversary), (jointSigAdvantage P B).toReal ≤ εsig)
    (hkem : ∀ (B : K.IND_CCA_Adversary),
      (KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B).toReal ≤ εkem)
    (haead : ∀ (B : AEAD.INT_CTXT_D_Adversary P.aead), AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (D : PRFScheme.PRFAdversary (Key × Key × Key × Option Key) (Key × Key × Key)),
      ((kdfPRF H).prfAdvantage D).toReal ≤ εkdf)
    (hpk : ∀ (pk : PQPub),
      (Pr{let y ← (fun x => x.public_key) <$> P.pqKeygen}[y = pk]).toReal ≤ εpk)
    : fullAdvantage P msg hasOPK A ≤ εsig + 2 * ↑q * (εkem + εaead + εkdf) + 3 * ↑q ^ 2 * εpk

/--
info: 'Protocols.PQXDH.uakeInitiator_secure_pq_total' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.uakeInitiator_secure_pq_total

recall Protocols.PQXDH.fullExp_noLostMass
    {Rand Msg C IdC IdK : Type} [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool) (hC : CoreContracts)
    (hS : SignatureContracts) (H : libsignal_protocol.crypto.HmacSha256)
    (hH : libsignal_protocol.crypto.HkdfSha256Contract H)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r)
    (A : AKE.UAKE.Adversary (uakeInitiator P EntryPoints.extracted msg hasOPK))
    (hA : Adversary.SendsFittingMessages A)
    : rustRuntime.prFail (fullExp P msg hasOPK A) = 0

/--
info: 'Protocols.PQXDH.fullExp_noLostMass' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.fullExp_noLostMass

/-! ## Correctness -/

recall Protocols.PQXDH.coreCompletion_extracted
    {Rand Msg C IdC IdK : Type} (P : Params Rand Msg C IdC IdK) (hasOPK : Bool) (hC : CoreContracts)
    (H : libsignal_protocol.crypto.HmacSha256) (hH : libsignal_protocol.crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom) (hCoins : ∀ r ∈ support P.coins, Dom r)
    : rustRuntime.evalDist (coreCompletionExp P EntryPoints.extracted hasOPK) {true} = 1

/--
info: 'Protocols.PQXDH.coreCompletion_extracted' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.coreCompletion_extracted

recall Protocols.PQXDH.jointKeyAgreement_extracted
    {Rand Msg C IdC IdK : Type} (P : Params Rand Msg C IdC IdK) (hasOPK : Bool) (hC : CoreContracts)
    (H : libsignal_protocol.crypto.HmacSha256) (hH : libsignal_protocol.crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom) (hCoins : ∀ r ∈ support P.coins, Dom r)
    (δ : ENNReal) (hδ : KyberDeltaCorrect P δ)
    : 1 - δ ≤ rustRuntime.evalDist (jointKeyExp P EntryPoints.extracted hasOPK) {true}

/--
info: 'Protocols.PQXDH.jointKeyAgreement_extracted' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.jointKeyAgreement_extracted

recall Protocols.PQXDH.wrapperAgreement_uakeInitiator
    {Rand Msg C IdC IdK : Type} [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool) (hC : CoreContracts)
    (hS : SignatureContracts) (H : libsignal_protocol.crypto.HmacSha256)
    (hH : libsignal_protocol.crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r) (hAead : AEAD.PerfectlyCorrect P.aead) (δ : ENNReal)
    (hδ : KyberDeltaCorrect P δ)
    : 1 - δ
      ≤ rustRuntime.evalDist
      (AKE.UAKE.agreementExp (uakeInitiator P EntryPoints.extracted msg hasOPK)) {true}

/--
info: 'Protocols.PQXDH.wrapperAgreement_uakeInitiator' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.wrapperAgreement_uakeInitiator

recall Protocols.PQXDH.wrapperAgreement_uakeRecipient
    {Rand Msg C IdC IdK : Type} [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool) (hC : CoreContracts)
    (hS : SignatureContracts) (H : libsignal_protocol.crypto.HmacSha256)
    (hH : libsignal_protocol.crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r) (hAead : AEAD.PerfectlyCorrect P.aead) (δ : ENNReal)
    (hδ : KyberDeltaCorrect P δ)
    : 1 - δ
      ≤ rustRuntime.evalDist
      (AKE.UAKE.agreementExp (uakeRecipient P EntryPoints.extracted msg hasOPK)) {true}

/--
info: 'Protocols.PQXDH.wrapperAgreement_uakeRecipient' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.wrapperAgreement_uakeRecipient

/-! ## Witness -/

recall Protocols.PQXDH.initiate_kdfInput_witness
    {Rand : Type} (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : libsignal_protocol.pqxdh.InitiatorParameters) (r r' : Rand) (ag : InitiatorAgreement)
    (h : libsignal_protocol.pqxdh.pqxdh_initiate rng crng ip r = Aeneas.Std.Result.ok
      (Aeneas.Std.core.result.Result.Ok ag, r'))
    : ∃ km, InitiateKdfInput crng ip r km ∧ libsignal_protocol.pqxdh.HandshakeKeys.derive km
      = Aeneas.Std.Result.ok ag.keys

/--
info: 'Protocols.PQXDH.initiate_kdfInput_witness' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.initiate_kdfInput_witness

recall Protocols.PQXDH.accept_kdfInput_witness
    (rp : libsignal_protocol.pqxdh.RecipientParameters) (hk : HandshakeKeys)
    (h : libsignal_protocol.pqxdh.pqxdh_accept rp = Aeneas.Std.Result.ok
      (Aeneas.Std.core.result.Result.Ok hk))
    : ∃ km, AcceptKdfInput rp km ∧ libsignal_protocol.pqxdh.HandshakeKeys.derive km
      = Aeneas.Std.Result.ok hk

/--
info: 'Protocols.PQXDH.accept_kdfInput_witness' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PublicKey.is_torsion_free,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.accept_kdfInput_witness

/-! ## Runtime and KEM correctness -/

recall Protocols.Realization.rustRuntime_coherent
    : AKE.UAKE.RuntimeCoherent rustRuntime

/--
info: 'Protocols.Realization.rustRuntime_coherent' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Realization.rustRuntime_coherent

recall Protocols.Realization.liftResult_bind
    {ι : Type} {O : OracleSpec ι} {α β : Type} (x : Aeneas.Std.Result α)
    (f : α → Aeneas.Std.Result β)
    : liftResult (x >>= f) = liftResult x >>= fun a => liftResult (f a)

/--
info: 'Protocols.Realization.liftResult_bind' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Realization.liftResult_bind

recall Protocols.Realization.liftResult_eq_pure_of_spec
    {ι : Type} {O : OracleSpec ι} {α : Type} {x : Aeneas.Std.Result α} {a : α}
    (h : Aeneas.Std.WP.spec x fun x => x = a)
    : liftResult x = pure a

/--
info: 'Protocols.Realization.liftResult_eq_pure_of_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Realization.liftResult_eq_pure_of_spec

recall Protocols.Realization.probOutput_rustRuntime
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : RustOracleComp unifSpec α) (a : α)
    : rustRuntime.evalDist mx {a} = Pr{let r ← ExceptT.run mx}[r = Except.ok a]

/--
info: 'Protocols.Realization.probOutput_rustRuntime' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Realization.probOutput_rustRuntime

recall Protocols.Realization.probFailure_rustRuntime
    {α : Type} [MeasurableSpace α] (mx : RustOracleComp unifSpec α)
    : rustRuntime.prFail mx = Pr{let r ← ExceptT.run mx}[r.toBool = false]

/--
info: 'Protocols.Realization.probFailure_rustRuntime' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Realization.probFailure_rustRuntime

recall KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect
    {m : Type → Type} [Monad m] {K PK SK C : Type} [DecidableEq K] (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m)
    : kem.correctnessError runtime = 0 ↔ kem.PerfectlyCorrect runtime

/--
info: 'KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect

recall KEMScheme.one_sub_le_probOutput_of_deltaCorrect
    {m : Type → Type} [Monad m] {K PK SK C : Type} [DecidableEq K] {kem : KEMScheme m K PK SK C}
    {runtime : ProbCompRuntime m} {δ : ENNReal} (h : kem.deltaCorrect runtime δ)
    : 1 - δ ≤ runtime.evalDist kem.correctnessExperiment {true}

/--
info: 'KEMScheme.one_sub_le_probOutput_of_deltaCorrect' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms KEMScheme.one_sub_le_probOutput_of_deltaCorrect

recall Protocols.PQXDH.kyberKem_correctExp_sound
    {Rand Msg C IdC IdK : Type} (P : Params Rand Msg C IdC IdK)
    (h : true ∈ support (kyberKem P).correctnessExperiment)
    : ∃ kp ∈ support P.pqKeygen, ∃ r ∈ support P.coins, ∃ ss ct r',
      libsignal_protocol.kem.KeyPublic.encapsulate P.cryptoRngInst kp.public_key r
      = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ss, ct), r')
      ∧ libsignal_protocol.kem.KeySecret.decapsulate kp.secret_key ct = Aeneas.Std.Result.ok
      (Aeneas.Std.core.result.Result.Ok ss)

/--
info: 'Protocols.PQXDH.kyberKem_correctExp_sound' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.kyberKem_correctExp_sound

recall Protocols.PQXDH.initiator_output_eq
    {Rand Msg C IdC IdK : Type} [DecidableEq Msg] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (st : InitiatorState Rand Msg)
    : (initiator P E).output st = pure (Option.map (fun j => some j.root) st.jointKeys) ∧
      (initiatorNoConfirm P E).output st = pure (Option.map (fun j => some j.root) st.jointKeys)

/--
info: 'Protocols.PQXDH.initiator_output_eq' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PublicKey.verify_signature_for_multipart_message,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.initiator_output_eq

recall Protocols.PQXDH.recipient_output_eq
    {Rand Msg C IdC IdK : Type} [DecidableEq IdC] [DecidableEq IdK] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (hasOPK : Bool) (st : RecipientState Msg)
    : (recipient P E hasOPK).output st = pure (Option.map (fun j => some j.root) st.jointKeys) ∧
      (recipientNoConfirm P E hasOPK).output st = pure
      (Option.map (fun j => some j.root) st.jointKeys)

/--
info: 'Protocols.PQXDH.recipient_output_eq' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_signature,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.recipient_output_eq

/-! ## Definitions -/

/--
info: 'Protocols.Realization.rustRuntime' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Realization.rustRuntime

/--
info: 'Protocols.Realization.liftResult' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Realization.liftResult

/--
info: 'Protocols.PQXDH.kyberKem' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.kyberKem

/--
info: 'Protocols.PQXDH.KyberDeltaCorrect' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.KyberDeltaCorrect

/--
info: 'Protocols.PQXDH.uakeInitiator' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.verify_signature_for_multipart_message,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.uakeInitiator

/--
info: 'Protocols.PQXDH.uakeRecipient' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.verify_signature_for_multipart_message,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.uakeRecipient

/--
info: 'Protocols.PQXDH.fullPartnering' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.fullPartnering

/--
info: 'Protocols.PQXDH.fullExp' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.fullExp

/--
info: 'Protocols.PQXDH.fullAdvantage' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.fullAdvantage

/--
info: 'Protocols.PQXDH.CoreContracts' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 Str.Insts.AllocBorrowToOwnedString.to_owned,
 alloc.vec.Vec.into_boxed_slice,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.CoreContracts

/--
info: 'Protocols.PQXDH.SignatureContracts' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.verify_signature_for_multipart_message]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.SignatureContracts

/--
info: 'Protocols.PQXDH.PartialContracts' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.is_torsion_free,
 curve.PublicKey.verify_signature_for_multipart_message,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 Slice.Insts.CoreCmpPartialEqArray.eq,
 alloc.vec.Vec.into_boxed_slice,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.PartialContracts

/--
info: 'Protocols.PQXDH.KyberBridge' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 BoxSlice.Insts.CoreConvertFromShared0Slice.from,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.KyberBridge

/--
info: 'Protocols.PQXDH.jointSigAdvantage' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.verify_signature_for_multipart_message]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.jointSigAdvantage

/--
info: 'Protocols.PQXDH.pqxdhODHAdvantage' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_agreement]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.pqxdhODHAdvantage

/--
info: 'Protocols.PQXDH.kdfPRF' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.kdfPRF

/--
info: 'Protocols.PQXDH.coreCompletionExp' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.coreCompletionExp

/--
info: 'Protocols.PQXDH.jointKeyExp' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.jointKeyExp

/--
info: 'AKE.UAKE.agreementExp' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AKE.UAKE.agreementExp

/--
info: 'Protocols.PQXDH.Adversary.SendsFittingMessages' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Adversary.SendsFittingMessages

/-! ## Key-derivation mirror

The Lean mirror of the key derivation in `Protocols/PQXDH/Kdf.lean` and the byte types and
projections of `Protocols/PQXDH/Defs.lean` that it uses. -/

recall Protocols.PQXDH.deriveKeysTotal (H : libsignal_protocol.crypto.HmacSha256)
    (h_hkdf : libsignal_protocol.crypto.HkdfSha256Contract H) : DeriveKeysTotal

/--
info: 'Protocols.PQXDH.deriveKeysTotal' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.deriveKeysTotal

open Aeneas Aeneas.Std Result in
recall Protocols.PQXDH.kdfInput_spec (dh1 dh2 dh3 : Slice U8) (dh4 : Option (Slice U8))
    (ss : Slice U8) (h_len : (kdfInputSliceBytes dh1 dh2 dh3 dh4 ss).length ≤ Usize.max) :
    kdfInput dh1 dh2 dh3 dh4 ss ⦃ inp => inp.val = kdfInputSliceBytes dh1 dh2 dh3 dh4 ss ⦄

/--
info: 'Protocols.PQXDH.kdfInput_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.kdfInput_spec

open Aeneas Aeneas.Std Result in
recall Protocols.PQXDH.kdfInput_fixed_spec (dh1 dh2 dh3 : Array U8 32#usize)
    (dh4 : Option (Array U8 32#usize)) (ss : Array U8 32#usize) :
    kdfInput dh1.to_slice dh2.to_slice dh3.to_slice (dh4.map (·.to_slice)) ss.to_slice
      ⦃ inp =>
        inp.val = kdfInputSliceBytes dh1.to_slice dh2.to_slice dh3.to_slice
          (dh4.map (·.to_slice)) ss.to_slice ∧
        inp.length = if dh4.isSome then 192 else 160 ⦄

/--
info: 'Protocols.PQXDH.kdfInput_fixed_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.kdfInput_fixed_spec

/--
info: 'Protocols.PQXDH.kdfInputSliceBytes' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.kdfInputSliceBytes

/--
info: 'Protocols.PQXDH.deriveHK' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.deriveHK

/--
info: 'Protocols.PQXDH.deriveKeys' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.deriveKeys

/--
info: 'Protocols.PQXDH.DeriveKeysTotal' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.DeriveKeysTotal

/--
info: 'Protocols.PQXDH.kdfInput' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.kdfInput

/--
info: 'Protocols.PQXDH.pubSlice' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.pubSlice

/--
info: 'Protocols.PQXDH.sliceOfKey' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.sliceOfKey

/--
info: 'Protocols.PQXDH.pubBytes' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.pubBytes

/--
info: 'Protocols.PQXDH.ECPub' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.ECPub

/--
info: 'Protocols.PQXDH.Key' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Key

/--
info: 'Protocols.PQXDH.HandshakeKeys' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.HandshakeKeys

/--
info: 'Protocols.PQXDH.rootKeyBytes' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.rootKeyBytes

/--
info: 'Protocols.PQXDH.chainKeyBytes' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.chainKeyBytes

/--
info: 'Protocols.PQXDH.pqrKeyBytes' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.pqrKeyBytes

/-- info: 'Protocols.PQXDH.Bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Bytes

/-! ## Score convention

Under the `ProbComp` runtime, the guess-form UAKE advantage is half the real-versus-random
advantage. No statement above uses `distAdvantage`. -/

recall AKE.UAKE.advantage_eq_distAdvantage_div_two {K UK TK W : Type} [SampleableType K]
    [DecidableEq W] {proto : AKE.UAKE.Scheme ProbComp K UK TK W} (A : AKE.UAKE.Adversary proto) :
    AKE.UAKE.advantage ProbCompRuntime.probComp A =
      AKE.UAKE.distAdvantage ProbCompRuntime.probComp A / 2

/--
info: 'AKE.UAKE.advantage_eq_distAdvantage_div_two' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AKE.UAKE.advantage_eq_distAdvantage_div_two
