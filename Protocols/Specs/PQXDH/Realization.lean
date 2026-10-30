/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Mathlib.Tactic.Recall
import Protocols.PQXDH.Realization.Correctness
import Protocols.PQXDH.Realization.Security

/-!
# Spec summary: the Full realization of PQXDH

This file freezes the headline statements of the Full realization. Each theorem is restated with
`recall`, which checks that the restatement is definitionally equal to the declared statement,
and each theorem and central definition has a `#guard_msgs` check on its axioms. The build fails
if a statement or its trust changes. A reader can check the statements here, together with the
definitions they mention, without reading the proofs.

The axioms of a statement list the opaque leaves of the extracted code that its definitions
mention (for example `curve.PrivateKey.calculate_agreement`), the native-decision axiom that the
extraction of `pqxdh_accept` introduces, and `sorryAx` when the proof, or a proof it uses, is a
stub. The stubs are of two kinds: temporary stubs of the correctness statements and their
supporting lemmas, to be proved first, and the security statements and
`fullExp_noLostMass`, which are placeholders for the security milestone. `Protocols/LEDGER.md`
lists both kinds apart from the admitted hops of the abstract model.

The fault fixtures, which show that the correctness statements are not vacuous, are in
`ProtocolsTest/PQXDH/Realization/FaultFixtures.lean` and carry their own axiom checks.
-/

open Protocols.PQXDH.Realization Protocols.Realization

/-! ## Security -/

/-! Each headline bound carries its fault term `Pr[⊥]`. The bound without
that term is recalled below it, with the totality premises it adds. -/

recall Protocols.PQXDH.Realization.uakeInitiator_secure_dh
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
    (hpk : ∀ (pk : PQPub), Pr[= pk | (fun x => x.public_key) <$> P.pqKeygen].toReal ≤ εpk)
    : fullAdvantage P msg hasOPK A ≤ εsig + 2 * ↑q * (εodh + 2 * εaead) + 3 * ↑q ^ 2 * εpk
      + Pr[⊥ | rustRuntime.evalDist (fullExp P msg hasOPK A)].toReal

/--
info: 'Protocols.PQXDH.Realization.uakeInitiator_secure_dh' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.uakeInitiator_secure_dh

recall Protocols.PQXDH.Realization.uakeInitiator_secure_dh_total
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
    (hpk : ∀ (pk : PQPub), Pr[= pk | (fun x => x.public_key) <$> P.pqKeygen].toReal ≤ εpk)
    : fullAdvantage P msg hasOPK A ≤ εsig + 2 * ↑q * (εodh + 2 * εaead) + 3 * ↑q ^ 2 * εpk

/--
info: 'Protocols.PQXDH.Realization.uakeInitiator_secure_dh_total' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.uakeInitiator_secure_dh_total

recall Protocols.PQXDH.Realization.uakeInitiator_secure_pq
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
    (hkem : ∀ (B : K.IND_CCA_Adversary), KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B
      ≤ εkem)
    (haead : ∀ (B : AEAD.INT_CTXT_D_Adversary P.aead), AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (D : PRFScheme.PRFAdversary (Key × Key × Key × Option Key) (Key × Key × Key)),
      (kdfPRF H).prfAdvantage D ≤ εkdf)
    (hpk : ∀ (pk : PQPub), Pr[= pk | (fun x => x.public_key) <$> P.pqKeygen].toReal ≤ εpk)
    : fullAdvantage P msg hasOPK A ≤ εsig + 2 * ↑q * (εkem + εaead + εkdf) + 3 * ↑q ^ 2 * εpk
      + Pr[⊥ | rustRuntime.evalDist (fullExp P msg hasOPK A)].toReal

/--
info: 'Protocols.PQXDH.Realization.uakeInitiator_secure_pq' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.uakeInitiator_secure_pq

recall Protocols.PQXDH.Realization.uakeInitiator_secure_pq_total
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
    (hkem : ∀ (B : K.IND_CCA_Adversary), KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B
      ≤ εkem)
    (haead : ∀ (B : AEAD.INT_CTXT_D_Adversary P.aead), AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdf : ∀ (D : PRFScheme.PRFAdversary (Key × Key × Key × Option Key) (Key × Key × Key)),
      (kdfPRF H).prfAdvantage D ≤ εkdf)
    (hpk : ∀ (pk : PQPub), Pr[= pk | (fun x => x.public_key) <$> P.pqKeygen].toReal ≤ εpk)
    : fullAdvantage P msg hasOPK A ≤ εsig + 2 * ↑q * (εkem + εaead + εkdf) + 3 * ↑q ^ 2 * εpk

/--
info: 'Protocols.PQXDH.Realization.uakeInitiator_secure_pq_total' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.uakeInitiator_secure_pq_total

recall Protocols.PQXDH.Realization.fullExp_noLostMass
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
    : Pr[⊥ | rustRuntime.evalDist (fullExp P msg hasOPK A)] = 0

/--
info: 'Protocols.PQXDH.Realization.fullExp_noLostMass' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.fullExp_noLostMass

/-! ## Correctness -/

recall Protocols.PQXDH.Realization.coreCompletion_extracted
    {Rand Msg C IdC IdK : Type} (P : Params Rand Msg C IdC IdK) (hasOPK : Bool) (hC : CoreContracts)
    (H : libsignal_protocol.crypto.HmacSha256) (hH : libsignal_protocol.crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom) (hCoins : ∀ r ∈ support P.coins, Dom r)
    : Pr[= true | rustRuntime.evalDist (coreCompletionExp P EntryPoints.extracted hasOPK)] = 1

/--
info: 'Protocols.PQXDH.Realization.coreCompletion_extracted' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.coreCompletion_extracted

recall Protocols.PQXDH.Realization.jointKeyAgreement_extracted
    {Rand Msg C IdC IdK : Type} (P : Params Rand Msg C IdC IdK) (hasOPK : Bool) (hC : CoreContracts)
    (H : libsignal_protocol.crypto.HmacSha256) (hH : libsignal_protocol.crypto.HkdfSha256Contract H)
    (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
    (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom) (hCoins : ∀ r ∈ support P.coins, Dom r)
    (δ : ENNReal) (hδ : KyberDeltaCorrect P δ)
    : 1 - δ ≤ Pr[= true | rustRuntime.evalDist (jointKeyExp P EntryPoints.extracted hasOPK)]

/--
info: 'Protocols.PQXDH.Realization.jointKeyAgreement_extracted' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.jointKeyAgreement_extracted

recall Protocols.PQXDH.Realization.wrapperAgreement_uakeInitiator
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
      ≤ Pr[= true | rustRuntime.evalDist
      (agreementExp (uakeInitiator P EntryPoints.extracted msg hasOPK))]

/--
info: 'Protocols.PQXDH.Realization.wrapperAgreement_uakeInitiator' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.wrapperAgreement_uakeInitiator

recall Protocols.PQXDH.Realization.wrapperAgreement_uakeRecipient
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
      ≤ Pr[= true | rustRuntime.evalDist
      (agreementExp (uakeRecipient P EntryPoints.extracted msg hasOPK))]

/--
info: 'Protocols.PQXDH.Realization.wrapperAgreement_uakeRecipient' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.wrapperAgreement_uakeRecipient

/-! ## Witness -/

recall Protocols.PQXDH.Realization.initiate_kdfInput_witness
    {Rand : Type} (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : libsignal_protocol.pqxdh.InitiatorParameters) (r r' : Rand) (ag : InitiatorAgreement)
    (h : libsignal_protocol.pqxdh.pqxdh_initiate rng crng ip r = Aeneas.Std.Result.ok
      (Aeneas.Std.core.result.Result.Ok ag, r'))
    : ∃ km, InitiateKdfInput crng ip r km ∧ libsignal_protocol.pqxdh.HandshakeKeys.derive km
      = Aeneas.Std.Result.ok ag.keys

/--
info: 'Protocols.PQXDH.Realization.initiate_kdfInput_witness' depends on axioms:
 [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 crypto.hkdf_sha256,
 curve.PrivateKey.calculate_agreement,
 alloc.vec.Vec.into_boxed_slice,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero,
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.initiate_kdfInput_witness

recall Protocols.PQXDH.Realization.accept_kdfInput_witness
    (rp : libsignal_protocol.pqxdh.RecipientParameters) (hk : HandshakeKeys)
    (h : libsignal_protocol.pqxdh.pqxdh_accept rp = Aeneas.Std.Result.ok
      (Aeneas.Std.core.result.Result.Ok hk))
    : ∃ km, AcceptKdfInput rp km ∧ libsignal_protocol.pqxdh.HandshakeKeys.derive km
      = Aeneas.Std.Result.ok hk

/--
info: 'Protocols.PQXDH.Realization.accept_kdfInput_witness' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.accept_kdfInput_witness

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
    {α : Type} (mx : RustOracleComp unifSpec α) (a : α)
    : Pr[= a | rustRuntime.evalDist mx] = Pr[= Except.ok a | ExceptT.run mx]

/--
info: 'Protocols.Realization.probOutput_rustRuntime' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.Realization.probOutput_rustRuntime

recall Protocols.Realization.probFailure_rustRuntime
    {α : Type} (mx : RustOracleComp unifSpec α)
    : Pr[⊥ | rustRuntime.evalDist mx] = probEvent (ExceptT.run mx) fun r => r.toBool = false

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
    : 1 - δ ≤ Pr[= true | runtime.evalDist kem.CorrectExp]

/--
info: 'KEMScheme.one_sub_le_probOutput_of_deltaCorrect' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms KEMScheme.one_sub_le_probOutput_of_deltaCorrect

recall Protocols.PQXDH.Realization.kyberKem_correctExp_sound
    {Rand Msg C IdC IdK : Type} (P : Params Rand Msg C IdC IdK)
    (h : true ∈ support (kyberKem P).CorrectExp)
    : ∃ kp ∈ support P.pqKeygen, ∃ r ∈ support P.coins, ∃ ss ct r',
      libsignal_protocol.kem.KeyPublic.encapsulate P.cryptoRngInst kp.public_key r
      = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok (ss, ct), r')
      ∧ libsignal_protocol.kem.KeySecret.decapsulate kp.secret_key ct = Aeneas.Std.Result.ok
      (Aeneas.Std.core.result.Result.Ok ss)

/--
info: 'Protocols.PQXDH.Realization.kyberKem_correctExp_sound' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.kyberKem_correctExp_sound

recall Protocols.PQXDH.Realization.initiator_output_eq
    {Rand Msg C IdC IdK : Type} [DecidableEq Msg] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (st : InitiatorState Rand Msg)
    : (initiator P E).output st = pure (Option.map (fun j => some j.root) st.jointKeys) ∧
      (initiatorNoConfirm P E).output st = pure (Option.map (fun j => some j.root) st.jointKeys)

/--
info: 'Protocols.PQXDH.Realization.initiator_output_eq' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.initiator_output_eq

recall Protocols.PQXDH.Realization.recipient_output_eq
    {Rand Msg C IdC IdK : Type} [DecidableEq IdC] [DecidableEq IdK] (P : Params Rand Msg C IdC IdK)
    (E : EntryPoints Rand) (hasOPK : Bool) (st : RecipientState Msg)
    : (recipient P E hasOPK).output st = pure (Option.map (fun j => some j.root) st.jointKeys) ∧
      (recipientNoConfirm P E hasOPK).output st = pure
      (Option.map (fun j => some j.root) st.jointKeys)

/--
info: 'Protocols.PQXDH.Realization.recipient_output_eq' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.recipient_output_eq

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
info: 'Protocols.PQXDH.Realization.kyberKem' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.kyberKem

/--
info: 'Protocols.PQXDH.Realization.KyberDeltaCorrect' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.KyberDeltaCorrect

/--
info: 'Protocols.PQXDH.Realization.uakeInitiator' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.uakeInitiator

/--
info: 'Protocols.PQXDH.Realization.uakeRecipient' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.uakeRecipient

/--
info: 'Protocols.PQXDH.Realization.fullPartnering' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.fullPartnering

/--
info: 'Protocols.PQXDH.Realization.fullExp' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.fullExp

/--
info: 'Protocols.PQXDH.Realization.fullAdvantage' depends on axioms:
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
 Aeneas.Std.core.fmt.Formatter,
 kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate,
 kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate,
 libsignal_protocol.pqxdh.pqxdh_accept._native.decide.ax_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.fullAdvantage

/--
info: 'Protocols.PQXDH.Realization.CoreContracts' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.CoreContracts

/--
info: 'Protocols.PQXDH.Realization.SignatureContracts' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_signature,
 curve.PrivateKey.public_key,
 curve.PublicKey.verify_signature_for_multipart_message]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.SignatureContracts

/--
info: 'Protocols.PQXDH.Realization.PartialContracts' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.PartialContracts

/--
info: 'Protocols.PQXDH.Realization.KyberBridge' depends on axioms:
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
#print axioms Protocols.PQXDH.Realization.KyberBridge

/--
info: 'Protocols.PQXDH.Realization.jointSigAdvantage' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_agreement,
 curve.PrivateKey.calculate_signature,
 curve.PublicKey.verify_signature_for_multipart_message]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.jointSigAdvantage

/--
info: 'Protocols.PQXDH.Realization.pqxdhODHAdvantage' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve.PrivateKey.calculate_agreement]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.pqxdhODHAdvantage

/--
info: 'Protocols.PQXDH.Realization.kdfPRF' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.kdfPRF

/--
info: 'Protocols.PQXDH.Realization.coreCompletionExp' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.coreCompletionExp

/--
info: 'Protocols.PQXDH.Realization.jointKeyExp' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 core.num.niche_types.NonZeroU8Inner,
 core.num.nonzero.NonZero]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.jointKeyExp

/--
info: 'Protocols.PQXDH.Realization.agreementExp' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.agreementExp

/--
info: 'Protocols.PQXDH.Realization.Adversary.SendsFittingMessages' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Protocols.PQXDH.Realization.Adversary.SendsFittingMessages
