import VersoManual
import VersoBlueprint.PreviewManifest
import LibsignalVerifyBlueprint.Blueprint
open Verso Doc
open Verso.Genre Manual
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc LibsignalVerifyBlueprint.Blueprint) args
    (extensionImpls := by exact extension_impls%)
    (config := { htmlDepth := 2, rootTocDepth := some 2 })
