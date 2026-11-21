import Libsignal.Translated.Core.Funs

open Aeneas Aeneas.Std

noncomputable abbrev libsignal_core.curve.PrivateKey.calculate_agreement :=
  _root_.curve.PrivateKey.calculate_agreement

noncomputable abbrev libsignal_core.curve.PublicKey.deserialize :=
  _root_.curve.PublicKey.deserialize

noncomputable abbrev libsignal_core.curve.PrivateKey.deserialize :=
  _root_.curve.PrivateKey.deserialize

noncomputable abbrev _root_.curve.KeyPair.generate :=
  @libsignal_core.curve.KeyPair.generate

noncomputable abbrev _root_.curve.PrivateKey.public_key :=
  libsignal_core.curve.PrivateKey.public_key

noncomputable abbrev libsignal_core.curve.PrivateKey.calculate_signature :=
  @_root_.curve.PrivateKey.calculate_signature

noncomputable abbrev libsignal_core.curve.PrivateKey.calculate_signature_for_multipart_message :=
  @_root_.curve.PrivateKey.calculate_signature_for_multipart_message

noncomputable abbrev libsignal_core.curve.PublicKey.verify_signature_for_multipart_message :=
  _root_.curve.PublicKey.verify_signature_for_multipart_message

noncomputable abbrev libsignal_core.curve.PublicKey.Insts.CoreConvertTryFromShared0SliceU8CurveError.try_from :=
  _root_.curve.PublicKey.Insts.CoreConvertTryFromShared0SliceU8CurveError.try_from
