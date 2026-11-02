/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/

import Lean.Elab.Import

/-! # Models dependency check

Checks the dependency rule of `Protocols/README.md`: no file under `Protocols/Models/` imports the
extraction (`Libsignal`) or a realisation. Inside the `Protocols` library, a model imports only
`Protocols.Models`, `Protocols.ToVCVio` and `Protocols.ToMathlib`.

The check reads each import header with Lean's own header parser, `Lean.Parser.parseHeader`, and
takes the imported modules from the result with `Lean.Elab.headerToImports`, as
`Lean.Elab.parseImports` does. So `public`, `meta`, `import all`, line breaks and comments in the
header count as they do for Lean, and an import that appears only in a comment is no import. A
header that does not parse fails the check.

Run from the repository root with `scripts/models-dependency-check.sh [ROOT]`, or with
`--self-test` for the fixed cases below. Not part of any Lake library. -/

open Lean

/-- The parts of the `Protocols` library that a model may import. -/
def allowedInProtocols : List Name := [`Protocols.Models, `Protocols.ToVCVio, `Protocols.ToMathlib]

/-- Whether a file under `Protocols/Models/` may import the module `m`. -/
def allowedImport (m : Name) : Bool :=
  if m.getRoot == `Libsignal then false
  else if m.getRoot == `Protocols then allowedInProtocols.any (·.isPrefixOf m)
  else true

/-- The prefix of every problem that reports a header parse error. -/
def parseError : String := "the import header does not parse"

/-- The problems in one file: its header parse errors, or else its forbidden imports. -/
def problems (fileName input : String) : IO (List String) := do
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext input fileName)
  if messages.hasErrors then
    let errors ← messages.toList.mapM (·.toString)
    return errors.map (s!"{parseError}: " ++ ·)
  return (Elab.headerToImports header).toList.filterMap fun i =>
    if allowedImport i.module then none else some s!"{fileName}: imports {i.module}"

/-- Checks every Lean file under `ROOT/Protocols/Models`. -/
def check (root : System.FilePath) : IO UInt32 := do
  let models := root / "Protocols" / "Models"
  unless (← models.isDir) do
    IO.println s!"No directory {models}"
    return 1
  let files := (← models.walkDir).filter (·.extension == some "lean")
  if files.isEmpty then
    IO.println s!"No Lean file under {models}"
    return 1
  let mut found : Array String := #[]
  for file in files.qsort (·.toString < ·.toString) do
    found := found ++ (← problems file.toString (← IO.FS.readFile file))
  if found.isEmpty then
    IO.println s!"Models dependency rule OK ({files.size} files)"
    return 0
  IO.println "Protocols/Models/ imports the extraction or a realisation:"
  found.forM IO.println
  return 1

/-- Headers that the rule accepts. The forbidden names occur only in comments and in the body. -/
def passingHeaders : List (String × String) := [
  ("plain", "import Mathlib.Data.Fintype.Basic\nimport VCVio.OracleComp.OracleComp\n\
    import Protocols.ToVCVio\nimport Protocols.ToMathlib\nimport Protocols.Models.PQXDH.Basic\n"),
  ("modifiers", "module\n\npublic import Protocols.ToVCVio\nmeta import Protocols.ToMathlib\n\
    import all Protocols.Models.PQXDH.Basic\npublic meta import Protocols.Models.PQXDH\n"),
  ("block-comment", "/-\nimport Protocols.PQXDH.Defs\nimport Libsignal\n-/\n\
    import Protocols.Models.PQXDH.Basic\n"),
  ("line-comment", "import Protocols.Models.PQXDH.Basic -- import Protocols.PQXDH.Defs\n\
    -- import all Libsignal.Translated.Protocol.Funs\n"),
  ("body", "import Protocols.Models.PQXDH.Basic\n\n\
    /-! Docs may name `import Protocols.PQXDH.Scheme`. -/\n\ndef x : Nat := 0\n")]

/-- Headers that the rule rejects, one for each way of writing a forbidden import. -/
def failingHeaders : List (String × String) := [
  ("libsignal", "import Protocols.ToVCVio\nimport Libsignal.Translated.Protocol.Funs\n"),
  ("realisation", "import Protocols.PQXDH.Scheme\n"),
  ("other-protocol", "import Protocols.X3DH.Scheme\n"),
  ("horizontal", "import Protocols.Realization.RustOracleComp\n"),
  ("specs", "import Protocols.Specs.PQXDH\n"),
  ("umbrella", "import Protocols\n"),
  ("near-prefix", "import Protocols.ModelsX.A\n"),
  ("public", "module\n\npublic import Protocols.PQXDH.Defs\n"),
  ("meta", "module\n\nmeta import Protocols.PQXDH.Defs\n"),
  ("all", "module\n\nimport all Protocols.PQXDH.Defs\n"),
  ("all-libsignal", "module\n\nimport all Libsignal.Translated.Protocol.Funs\n"),
  ("public-meta", "module\n\npublic meta import Protocols.Realization.RustOracleComp\n"),
  ("split", "import\n  Protocols.PQXDH.Defs\n"),
  ("split-modifiers", "module\n\npublic\nmeta\nimport\nProtocols.PQXDH.Defs\n"),
  ("split-all", "module\n\nimport\nall\nProtocols.PQXDH.Defs\n"),
  ("block-comment-inside", "import /- note -/ Protocols.PQXDH.Defs\n"),
  ("line-comment-inside", "import -- note\n  Protocols.PQXDH.Defs\n"),
  ("after-comment", "/- note -/ import Protocols.PQXDH.Defs\n"),
  ("after-module", "module import Protocols.PQXDH.Defs\n"),
  ("same-line", "import Protocols.Models.PQXDH.Basic import Protocols.PQXDH.Defs\n"),
  ("quoted", "import «Protocols».PQXDH.Defs\n")]

/-- Headers that do not parse. The check rejects them whatever they import. `public-all` relies on
a restriction of the pinned Lean 4.31 parser, which rejects `all` after `public import`. -/
def brokenHeaders : List (String × String) := [
  ("no-module", "import\n"),
  ("public-all", "module\n\npublic import all Protocols.Models.PQXDH.Basic\n")]

/-- Checks the rule on `passingHeaders`, `failingHeaders` and `brokenHeaders`. A failing header
must be rejected for its import, and a broken header for its parse error. -/
def selfTest : IO UInt32 := do
  let mut status : UInt32 := 0
  for (name, input) in passingHeaders do
    let found ← problems name input
    unless found.isEmpty do
      IO.println s!"self-test: the passing header '{name}' was rejected: {found}"
      status := 1
  for (name, input) in failingHeaders do
    unless (← problems name input).any (·.startsWith s!"{name}: imports ") do
      IO.println s!"self-test: the failing header '{name}' was not rejected for its import"
      status := 1
  for (name, input) in brokenHeaders do
    unless (← problems name input).any (·.startsWith parseError) do
      IO.println s!"self-test: the broken header '{name}' was not rejected as unparsable"
      status := 1
  if status == 0 then IO.println "Models dependency self-test OK"
  return status

def main : List String → IO UInt32
  | ["--self-test"] => selfTest
  | [] => check "."
  | [root] => check root
  | _ => do
    IO.println "usage: scripts/models-dependency-check.sh [ROOT | --self-test]"
    return 2
