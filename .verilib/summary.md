# Verification report: unknown unknown

## 1. Verified public API functions (0)

None

## 2. Trusted public API functions (0)

None

## 3. Trust base

### 3a. Properties assumed to hold (120 axioms)

Axioms — propositions assumed without proof.

- `probe:Bool.Insts.CoreConvertFromChoice.from`
- `probe:Slice.Insts.CoreCmpPartialEqArray.eq`
- `probe:Slice.Insts.SubtleConstantTimeEq.ct_eq`
- `probe:U8.Insts.SubtleConstantTimeEq.ct_eq`
- `probe:aes.autodetect.Aes256`
- `probe:aes_cbc.aes_256_cbc_decrypt`
- `probe:aes_cbc.aes_256_cbc_encrypt`
- `probe:aes_ctr.Aes256Ctr32`
- `probe:aes_ctr.Aes256Ctr32.from_key`
- `probe:aes_ctr.Aes256Ctr32.new`
- `probe:aes_ctr.Aes256Ctr32.process`
- `probe:aes_gcm.Aes256GcmDecryption.new`
- `probe:aes_gcm.Aes256GcmEncryption.new`
- `probe:aes_gcm.GcmGhash.finalize`
- `probe:aes_gcm.GcmGhash.update`
- `probe:alloc.string.String.Insts.CoreOpsDerefDerefStr.deref`
- `probe:alloc.vec.Vec.into_boxed_slice`
- `probe:cipher.stream_wrapper.StreamCipherCoreWrapper`
- `probe:core.num.error.TryFromIntError`
- `probe:core.num.niche_types.NonZeroU64Inner`
- `probe:core.num.niche_types.NonZeroU8Inner`
- `probe:core.num.nonzero.NonZero`
- `probe:core.num.nonzero.NonZero.get`
- `probe:core.num.nonzero.NonZero.new`
- `probe:core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual`
- `probe:core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch`
- `probe:core.option.Option.map`
- `probe:core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual`
- `probe:core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch`
- `probe:core.result.Result.ok`
- `probe:ctr.ctr_core.CtrCore`
- `probe:ctr.flavors.ctr32.Ctr32BE.Insts.CtrFlavorsCtrFlavorBCtrNonce32U32Clause0_ArrayTypeTryFromIntErrorInfallibleTryFromIntErrorTryFromIntErrorTryFromIntErrorTryFromIntErrorInfallibleInfallibleInfallibleTryFromIntError.NAME`
- `probe:ctr.flavors.ctr32.CtrNonce32`
- `probe:derive_more.convert.try_from.TryFromReprError.new`
- `probe:generic_array.GenericArray`
- `probe:generic_array.GenericArrayImplEven`
- `probe:generic_array.GenericArrayImplOdd`
- `probe:ghash.GHash`
- `probe:ghash.GHash.Insts.CoreCloneClone.clone`
- `probe:hash.CryptographicHash`
- `probe:hash.CryptographicHash.finalize`
- `probe:hash.CryptographicHash.new`
- `probe:hash.CryptographicHash.update`
- `probe:hash.CryptographicMac`
- `probe:hash.CryptographicMac.finalize`
- `probe:hash.CryptographicMac.new`
- `probe:hash.CryptographicMac.update`
- `probe:inout.inout.InOut`
- `probe:libsignal_core.curve.PrivateKey.Insts.CoreConvertTryFromShared0SliceU8CurveError.try_from`
- `probe:libsignal_core.curve.PublicKey.Insts.CoreConvertTryFromShared0SliceU8CurveError.try_from`
- `probe:libsignal_core.curve.PublicKey.is_torsion_free`
- `probe:libsignal_core.curve.PublicKey.verify_signature_for_multipart_message`
- `probe:signal_crypto.core.num.niche_types.NonZeroU64Inner.Insts.CoreCloneClone.clone`
- `probe:signal_crypto.core.num.niche_types.NonZeroU8Inner.Insts.CoreCloneClone.clone`
- `probe:subtle.Choice`
- `probe:typenum.bit.B0.Insts.CoreCloneClone.clone`
- `probe:typenum.bit.B0.Insts.CoreDefaultDefault.default`
- `probe:typenum.bit.B0.Insts.TypenumMarker_traitsBit.BOOL`
- `probe:typenum.bit.B0.Insts.TypenumMarker_traitsBit.U8`
- `probe:typenum.bit.B0.Insts.TypenumMarker_traitsBit.new`
- `probe:typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_bool`
- `probe:typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_u8`
- `probe:typenum.bit.B1.Insts.CoreCloneClone.clone`
- `probe:typenum.bit.B1.Insts.CoreDefaultDefault.default`
- `probe:typenum.bit.B1.Insts.TypenumMarker_traitsBit.BOOL`
- `probe:typenum.bit.B1.Insts.TypenumMarker_traitsBit.U8`
- `probe:typenum.bit.B1.Insts.TypenumMarker_traitsBit.new`
- `probe:typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_bool`
- `probe:typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_u8`
- `probe:typenum.private.InvertedUInt`
- `probe:typenum.uint.UInt`
- `probe:typenum.uint.UInt.Insts.CoreCloneClone.clone`
- `probe:typenum.uint.UInt.Insts.CoreDefaultDefault.default`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I16`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I32`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I64`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I8`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.ISIZE`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U16`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U32`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U64`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U8`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.USIZE`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i16`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i32`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i64`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i8`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_isize`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u16`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u32`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u64`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u8`
- `probe:typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_usize`
- `probe:typenum.uint.UTerm.Insts.CoreCloneClone.clone`
- `probe:typenum.uint.UTerm.Insts.CoreDefaultDefault.default`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I16`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I32`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I64`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I8`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.ISIZE`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U16`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U32`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U64`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U8`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.USIZE`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i16`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i32`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i64`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i8`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_isize`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u16`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u32`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u64`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u8`
- `probe:typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_usize`
- `probe:uuid.Uuid`
- `probe:uuid.Uuid.as_bytes`
- `probe:uuid.builder.Uuid.from_bytes`
- `probe:uuid.builder.Uuid.from_slice`
- `probe:uuid.error.Error`

### 3b. External functions assumed correct w.r.t. their specs (0)

None

## 4. Unverified and failed functions (0)

None

## 5. Verified remaining Lean functions (224)

- `probe:instDiscriminantCurveErrorIsize`
- `probe:instDiscriminantDecryptionErrorIsize`
- `probe:instDiscriminantEncryptionErrorIsize`
- `probe:instDiscriminantErrorIsize`
- `probe:instDiscriminantKeyTypeIsize`
- `probe:instDiscriminantPadTypeIsize`
- `probe:instDiscriminantPrivateKeyDataIsize`
- `probe:instDiscriminantPublicKeyDataIsize`
- `probe:instDiscriminantServiceIdIsize`
- `probe:instDiscriminantServiceIdKindU8`
- `probe:signal_crypto.U64.Insts.CoreNumNonzeroPrivateSealed`
- `probe:signal_crypto.U64.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroU64Inner`
- `probe:signal_crypto.U8.Insts.CoreConvertFromServiceIdKind`
- `probe:signal_crypto.U8.Insts.CoreConvertFromServiceIdKind.from`
- `probe:signal_crypto.U8.Insts.CoreNumNonzeroPrivateSealed`
- `probe:signal_crypto.U8.Insts.CoreNumNonzeroZeroablePrimitiveNonZeroU8Inner`
- `probe:signal_crypto.U8.Insts.SubtleConstantTimeEq`
- `probe:signal_crypto.aes_cbc.DecryptionError.read_discriminant`
- `probe:signal_crypto.aes_cbc.EncryptionError.read_discriminant`
- `probe:signal_crypto.aes_ctr.Aes256Ctr32.NONCE_SIZE`
- `probe:signal_crypto.aes_gcm.Aes256GcmDecryption.NONCE_SIZE`
- `probe:signal_crypto.aes_gcm.Aes256GcmDecryption.TAG_SIZE`
- `probe:signal_crypto.aes_gcm.Aes256GcmDecryption.ctr`
- `probe:signal_crypto.aes_gcm.Aes256GcmDecryption.decrypt`
- `probe:signal_crypto.aes_gcm.Aes256GcmDecryption.ghash`
- `probe:signal_crypto.aes_gcm.Aes256GcmDecryption.verify_tag`
- `probe:signal_crypto.aes_gcm.Aes256GcmEncryption.NONCE_SIZE`
- `probe:signal_crypto.aes_gcm.Aes256GcmEncryption.TAG_SIZE`
- `probe:signal_crypto.aes_gcm.Aes256GcmEncryption.compute_tag`
- `probe:signal_crypto.aes_gcm.Aes256GcmEncryption.ctr`
- `probe:signal_crypto.aes_gcm.Aes256GcmEncryption.encrypt`
- `probe:signal_crypto.aes_gcm.Aes256GcmEncryption.ghash`
- `probe:signal_crypto.aes_gcm.GcmGhash.Insts.CoreCloneClone.clone`
- `probe:signal_crypto.aes_gcm.GcmGhash.ad_len`
- `probe:signal_crypto.aes_gcm.GcmGhash.ghash`
- `probe:signal_crypto.aes_gcm.GcmGhash.ghash_pad`
- `probe:signal_crypto.aes_gcm.GcmGhash.msg_buf`
- `probe:signal_crypto.aes_gcm.GcmGhash.msg_buf_offset`
- `probe:signal_crypto.aes_gcm.GcmGhash.msg_len`
- `probe:signal_crypto.aes_gcm.NONCE_SIZE`
- `probe:signal_crypto.aes_gcm.TAG_SIZE`
- `probe:signal_crypto.block_padding.PadType.read_discriminant`
- `probe:signal_crypto.block_padding.Padding.TYPE`
- `probe:signal_crypto.block_padding.Padding.generic_arrayArrayLengthBlockSizeU8Self_Clause0_ArrayTypeInst`
- `probe:signal_crypto.block_padding.Padding.pad`
- `probe:signal_crypto.block_padding.Padding.unpad`
- `probe:signal_crypto.block_padding.UnpadError`
- `probe:signal_crypto.cipher.block.BlockBackend.crypto_commonParBlocksSizeUserInst`
- `probe:signal_crypto.cipher.block.BlockBackend.proc_block`
- `probe:signal_crypto.cipher.block.BlockCipher.crypto_commonBlockSizeUserInst`
- `probe:signal_crypto.cipher.block.BlockClosure.call`
- `probe:signal_crypto.cipher.block.BlockClosure.crypto_commonBlockSizeUserInst`
- `probe:signal_crypto.cipher.block.BlockEncrypt.crypto_commonBlockSizeUserInst`
- `probe:signal_crypto.cipher.block.BlockEncrypt.encrypt_with_backend`
- `probe:signal_crypto.cipher.block.BlockEncryptMut.crypto_commonBlockSizeUserInst`
- `probe:signal_crypto.cipher.block.BlockEncryptMut.encrypt_with_backend_mut`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryFromSelfI32Self_Clause0_ErrorInst`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryFromSelfU128Self_Clause3_ErrorInst`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryFromSelfU32Self_Clause1_ErrorInst`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryFromSelfU64Self_Clause2_ErrorInst`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryFromSelfUsizeSelf_Clause4_ErrorInst`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryIntoSelfI32Self_Clause5_ErrorInst`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryIntoSelfU128Self_Clause8_ErrorInst`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryIntoSelfU32Self_Clause6_ErrorInst`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryIntoSelfU64Self_Clause7_ErrorInst`
- `probe:signal_crypto.cipher.stream_core.Counter.coreconvertTryIntoSelfUsizeSelf_Clause9_ErrorInst`
- `probe:signal_crypto.core.num.niche_types.NonZeroU64Inner.Insts.CoreCloneClone`
- `probe:signal_crypto.core.num.niche_types.NonZeroU64Inner.Insts.CoreMarkerCopy`
- `probe:signal_crypto.core.num.niche_types.NonZeroU8Inner.Insts.CoreCloneClone`
- `probe:signal_crypto.core.num.niche_types.NonZeroU8Inner.Insts.CoreMarkerCopy`
- `probe:signal_crypto.core.num.nonzero.ZeroablePrimitive.markerCopyInst`
- `probe:signal_crypto.core.num.nonzero.ZeroablePrimitive.markerCopyInst1`
- `probe:signal_crypto.core.num.nonzero.ZeroablePrimitive.privateSealedInst`
- `probe:signal_crypto.core.ops.arith.Add.add`
- `probe:signal_crypto.core.ops.arith.Div.div`
- `probe:signal_crypto.core.ops.arith.Rem.rem`
- `probe:signal_crypto.core.ops.arith.Sub.sub`
- `probe:signal_crypto.core.ops.bit.Shl.shl`
- `probe:signal_crypto.crypto_common.BlockSizeUser.generic_arrayArrayLengthSelf_BlockSizeU8Self_Clause0_ArrayTypeInst`
- `probe:signal_crypto.crypto_common.ParBlocksSizeUser.BlockSizeUserInst`
- `probe:signal_crypto.crypto_common.ParBlocksSizeUser.generic_arrayArrayLengthSelf_ParBlocksSizeGenericArrayU8Self_Clause0_BlockSizeSelf_Clause0_Clause0_ArrayTypeSelf_Clause1_ArrayTypeInst`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.NAME`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.as_backend`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.cipherstream_coreCounterInst`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.corecloneCloneInst`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.current_block`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.from_nonce`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.generic_arrayArrayLengthBU8Self_Clause0_ArrayTypeInst`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.next_block`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.remaining`
- `probe:signal_crypto.ctr.flavors.CtrFlavor.set_from_backend`
- `probe:signal_crypto.derive_more.convert.try_from.TryFromReprError.input`
- `probe:signal_crypto.error.Error.read_discriminant`
- `probe:signal_crypto.generic_array.ArrayLength.typenummarker_traitsUnsignedInst`
- `probe:signal_crypto.hash.CryptographicMac.update_and_get`
- `probe:signal_crypto.libsignal_core.address.DeviceId.id`
- `probe:signal_crypto.libsignal_core.address.DeviceId.new_nonzero`
- `probe:signal_crypto.libsignal_core.address.InvalidDeviceId`
- `probe:signal_crypto.libsignal_core.address.MAX_VALID_DEVICE_ID`
- `probe:signal_crypto.libsignal_core.address.ProtocolAddress.device_id`
- `probe:signal_crypto.libsignal_core.address.ProtocolAddress.name`
- `probe:signal_crypto.libsignal_core.address.ServiceId.kind`
- `probe:signal_crypto.libsignal_core.address.ServiceId.parse_from_service_id_binary`
- `probe:signal_crypto.libsignal_core.address.ServiceId.parse_from_service_id_fixed_width_binary`
- `probe:signal_crypto.libsignal_core.address.ServiceId.raw_uuid`
- `probe:signal_crypto.libsignal_core.address.ServiceId.read_discriminant`
- `probe:signal_crypto.libsignal_core.address.ServiceId.service_id_binary`
- `probe:signal_crypto.libsignal_core.address.ServiceId.service_id_fixed_width_binary`
- `probe:signal_crypto.libsignal_core.address.ServiceIdKind.Insts.CoreCmpPartialEqServiceIdKind.eq`
- `probe:signal_crypto.libsignal_core.address.ServiceIdKind.Insts.CoreConvertTryFromU8TryFromReprErrorU8.try_from`
- `probe:signal_crypto.libsignal_core.address.ServiceIdKind.read_discriminant`
- `probe:signal_crypto.libsignal_core.address.SpecificServiceId.Insts.CoreConvertFromUuid`
- `probe:signal_crypto.libsignal_core.address.SpecificServiceId.Insts.CoreConvertFromUuid.from`
- `probe:signal_crypto.libsignal_core.address.SpecificServiceId.from_uuid`
- `probe:signal_crypto.libsignal_core.address.SpecificServiceId.uuid`
- `probe:signal_crypto.libsignal_core.curve.CurveError.read_discriminant`
- `probe:signal_crypto.libsignal_core.curve.KeyPair.private_key`
- `probe:signal_crypto.libsignal_core.curve.KeyPair.public_key`
- `probe:signal_crypto.libsignal_core.curve.KeyType.read_discriminant`
- `probe:signal_crypto.libsignal_core.curve.KeyType.value`
- `probe:signal_crypto.libsignal_core.curve.PrivateKey.key`
- `probe:signal_crypto.libsignal_core.curve.PrivateKeyData.read_discriminant`
- `probe:signal_crypto.libsignal_core.curve.PublicKey.key`
- `probe:signal_crypto.libsignal_core.curve.PublicKey.key_type`
- `probe:signal_crypto.libsignal_core.curve.PublicKey.scalar_is_in_range`
- `probe:signal_crypto.libsignal_core.curve.PublicKeyData.read_discriminant`
- `probe:signal_crypto.libsignal_core.e164.E164.from_be_bytes.closure`
- `probe:signal_crypto.libsignal_core.e164.E164.from_be_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleNonZeroU64NonZeroU64InnerE164`
- `probe:signal_crypto.libsignal_core.e164.E164.from_be_bytes.closure.Insts.CoreOpsFunctionFnOnceTupleNonZeroU64NonZeroU64InnerE164.call_once`
- `probe:signal_crypto.libsignal_core.e164.E164.inner`
- `probe:signal_crypto.libsignal_core.version.VERSION`
- `probe:signal_crypto.rand.distr.StandardUniform`
- `probe:signal_crypto.rand.distr.distribution.Distribution.sample`
- `probe:signal_crypto.rand.rng.Fill.fill`
- `probe:signal_crypto.rand.rng.Rng.rand_coreRngCoreInst`
- `probe:signal_crypto.rand_core.CryptoRng.RngCoreInst`
- `probe:signal_crypto.rand_core.RngCore.fill_bytes`
- `probe:signal_crypto.rand_core.RngCore.next_u32`
- `probe:signal_crypto.rand_core.RngCore.next_u64`
- `probe:signal_crypto.subtle.ConstantTimeEq.ct_eq`
- `probe:signal_crypto.typenum.Equal`
- `probe:signal_crypto.typenum.Greater`
- `probe:signal_crypto.typenum.Less`
- `probe:signal_crypto.typenum.bit.B0`
- `probe:signal_crypto.typenum.bit.B0.Insts.CoreCloneClone`
- `probe:signal_crypto.typenum.bit.B0.Insts.CoreDefaultDefault`
- `probe:signal_crypto.typenum.bit.B0.Insts.CoreMarkerCopy`
- `probe:signal_crypto.typenum.bit.B0.Insts.TypenumMarker_traitsBit`
- `probe:signal_crypto.typenum.bit.B0.Insts.TypenumSealedSealed`
- `probe:signal_crypto.typenum.bit.B1`
- `probe:signal_crypto.typenum.bit.B1.Insts.CoreCloneClone`
- `probe:signal_crypto.typenum.bit.B1.Insts.CoreDefaultDefault`
- `probe:signal_crypto.typenum.bit.B1.Insts.CoreMarkerCopy`
- `probe:signal_crypto.typenum.bit.B1.Insts.TypenumMarker_traitsBit`
- `probe:signal_crypto.typenum.bit.B1.Insts.TypenumSealedSealed`
- `probe:signal_crypto.typenum.marker_traits.Bit.BOOL`
- `probe:signal_crypto.typenum.marker_traits.Bit.U8`
- `probe:signal_crypto.typenum.marker_traits.Bit.coredefaultDefaultInst`
- `probe:signal_crypto.typenum.marker_traits.Bit.coremarkerCopyInst`
- `probe:signal_crypto.typenum.marker_traits.Bit.new`
- `probe:signal_crypto.typenum.marker_traits.Bit.sealedSealedInst`
- `probe:signal_crypto.typenum.marker_traits.Bit.to_bool`
- `probe:signal_crypto.typenum.marker_traits.Bit.to_u8`
- `probe:signal_crypto.typenum.marker_traits.NonZero.sealedSealedInst`
- `probe:signal_crypto.typenum.marker_traits.Ord.sealedSealedInst`
- `probe:signal_crypto.typenum.marker_traits.Ord.to_ordering`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.I16`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.I32`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.I64`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.I8`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.ISIZE`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.U16`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.U32`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.U64`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.U8`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.USIZE`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.coredefaultDefaultInst`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.coremarkerCopyInst`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.sealedSealedInst`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_i16`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_i32`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_i64`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_i8`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_isize`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_u16`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_u32`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_u64`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_u8`
- `probe:signal_crypto.typenum.marker_traits.Unsigned.to_usize`
- `probe:signal_crypto.typenum.private.Invert.invert`
- `probe:signal_crypto.typenum.private.InvertedUTerm`
- `probe:signal_crypto.typenum.private.InvertedUnsigned.to_u64`
- `probe:signal_crypto.typenum.private.IsLessPrivate.is_less_private`
- `probe:signal_crypto.typenum.private.IsLessPrivate.marker_traitsBitInst`
- `probe:signal_crypto.typenum.private.PrivateCmp.private_cmp`
- `probe:signal_crypto.typenum.private.PrivateDiv.private_div_quotient`
- `probe:signal_crypto.typenum.private.PrivateDiv.private_div_remainder`
- `probe:signal_crypto.typenum.private.PrivateDivIf.private_div_if_quotient`
- `probe:signal_crypto.typenum.private.PrivateDivIf.private_div_if_remainder`
- `probe:signal_crypto.typenum.private.PrivateInvert.private_invert`
- `probe:signal_crypto.typenum.private.PrivateSetBit.private_set_bit`
- `probe:signal_crypto.typenum.private.Trim.trim`
- `probe:signal_crypto.typenum.private.TrimTrailingZeros.trim_trailing_zeros`
- `probe:signal_crypto.typenum.type_operators.Cmp.compare`
- `probe:signal_crypto.typenum.type_operators.IsLess.is_less`
- `probe:signal_crypto.typenum.type_operators.IsLess.marker_traitsBitInst`
- `probe:signal_crypto.typenum.type_operators.Len.len`
- `probe:signal_crypto.typenum.type_operators.Len.marker_traitsUnsignedInst`
- `probe:signal_crypto.typenum.type_operators.PartialDiv.partial_div`
- `probe:signal_crypto.typenum.uint.GetBit.get_bit`
- `probe:signal_crypto.typenum.uint.SetBit.set_bit`
- `probe:signal_crypto.typenum.uint.UInt.Insts.CoreCloneClone`
- `probe:signal_crypto.typenum.uint.UInt.Insts.CoreDefaultDefault`
- `probe:signal_crypto.typenum.uint.UInt.Insts.CoreMarkerCopy`
- `probe:signal_crypto.typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned`
- `probe:signal_crypto.typenum.uint.UInt.Insts.TypenumSealedSealed`
- `probe:signal_crypto.typenum.uint.UTerm`
- `probe:signal_crypto.typenum.uint.UTerm.Insts.CoreCloneClone`
- `probe:signal_crypto.typenum.uint.UTerm.Insts.CoreDefaultDefault`
- `probe:signal_crypto.typenum.uint.UTerm.Insts.CoreMarkerCopy`
- `probe:signal_crypto.typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned`
- `probe:signal_crypto.typenum.uint.UTerm.Insts.TypenumSealedSealed`
- `probe:signal_crypto.uuid.Uuid.Insts.CoreConvertFromSpecificServiceId`
- `probe:signal_crypto.uuid.Uuid.Insts.CoreConvertFromSpecificServiceId.from`

## 6. Verified lemmas (0)

None

## 7. Out-of-scope public API functions (0)

Public API functions that Lean (via Aeneas) did not process.

None

---

## Public API accounting

| Category | Count |
|----------|------:|
| Verified public API | 0 |
| Trusted public API | 0 |
| Out-of-scope public API | 0 |
| **Total public API** | **0** |
