import VersoManual
import VersoBlueprint

open Lean Verso Doc Elab
open Verso.Genre.Manual
open Verso.Code.External
open SubVerso.Highlighting
open Verso.Output.Html

namespace LibsignalVerifyBlueprint

/-- Source links for VCVio declarations: the commit pinned in the root `lakefile.toml`. -/
def vcvioSourceUrl : String :=
  "https://github.com/Verified-zkEVM/VCV-io/blob/88efe9715a9fa9e7d89635c38cf70259836766c2/"

/-- Source links for this repository's declarations: the commit the book describes. -/
def repositorySourceUrl : String :=
  "https://github.com/Beneficial-AI-Foundation/libsignal-verify/blob/264b746ee3883a85466b73ffdc6081a005a00794/"

/-- Source links for cslib declarations: the commit pinned in the root manifest. -/
def cslibSourceUrl : String :=
  "https://github.com/leanprover/cslib/blob/5b56df99362532c46e1175381fbbdd755bd56030/"

/-- Where the source of a module lives: the local file the card is checked against (Lake runs
the elaborator in `docs/`, whose parent is the repository root) and the public URL it links to.
Only the packages listed here have source links. -/
def moduleSource (modName : String) : Option (String × String) :=
  let modulePath := modName.replace "." "/" ++ ".lean"
  if ["VCVio.", "ToMathlib.", "Examples."].any (fun (p : String) => modName.startsWith p) then
    some (".lake/packages/VCVio/" ++ modulePath, vcvioSourceUrl ++ modulePath)
  else if modName.startsWith "Cslib." then
    some (".lake/packages/cslib/" ++ modulePath, cslibSourceUrl ++ modulePath)
  else if modName.startsWith "Protocols." then
    some ("../" ++ modulePath, repositorySourceUrl ++ modulePath)
  else none

structure DeclarationConfig where
  name : Name
  part : String := "full"
  docstrings : Bool := true

instance {m : Type → Type} [Monad m] [MonadError m] :
    Verso.ArgParse.FromArgs DeclarationConfig m where
  fromArgs := DeclarationConfig.mk <$> .positional `name .name <*>
    .namedD `part .string "full" <*> .flag `docstrings true

/-- Keep a source interval while retaining token hovers and tactic-goal data. -/
private partial def window (hl : Highlighted) (start stop : Nat) : Highlighted :=
  if stop <= start then .empty else
  match hl with
  | .text s => .text <| SubVerso.Compat.String.take
      (SubVerso.Compat.String.drop s start) (stop - start)
  | .unparsed s => .unparsed <| SubVerso.Compat.String.take
      (SubVerso.Compat.String.drop s start) (stop - start)
  | .token tok =>
      let text := SubVerso.Compat.String.take
        (SubVerso.Compat.String.drop tok.content start) (stop - start)
      if text.isEmpty then .empty else .token { tok with content := text }
  -- Point annotations contain compiler messages, but no source characters.
  -- Verso renders their message bodies as text, so they do not belong in a
  -- declaration-source panel. Token hovers and tactic states remain below.
  | .point .. => .empty
  | .span info content =>
      let kept := window content start stop
      if kept.isEmpty then .empty else .span info kept
  | .tactics info first last content =>
      let kept := window content start stop
      if kept.isEmpty then .empty else .tactics info first last kept
  | .seq children => Id.run do
      let mut offset := 0
      let mut out := #[]
      for child in children do
        let width := child.toString.length
        if (width == 0 && start <= offset && offset < stop) ||
            (offset < stop && start < offset + width) then
          out := out.push (window child (start - offset) (stop - offset))
        offset := offset + width
      return .seq out

#guard (window (.point .warning (.text "diagnostic, not source")) 0 1).isEmpty
#guard (window (.seq #[.text "a", .point .warning (.text "diagnostic"), .text "b"]) 0 2).toString == "ab"

/-- Read the original spelling of a highlighted leaf. SubVerso normalizes
identifier names, so a token may omit the source's guillemets. No other
character difference is accepted. -/
private def sourceLeaf (expected : String) (identifier : Bool) :
    StateT (List Char) (Except String) String := do
  if expected.isEmpty then return ""
  let mut out := ""
  for c in expected.toList do
    let mut remaining ← get
    if identifier then
      while remaining.head? != some c &&
          (remaining.head? == some '«' || remaining.head? == some '»') do
        out := out.push remaining.head!
        remaining := remaining.tail!
    match remaining with
    | actual :: rest =>
      unless actual == c do
        throw s!"Source token mismatch: expected '{c}', found '{actual}'"
      out := out.push actual
      set rest
    | [] => throw "Source ended before the highlighted declaration"
  if identifier then
    while (← get).head? == some '»' do
      out := out.push '»'
      modify List.tail!
  return out

private partial def sourceTokens : Highlighted → StateT (List Char) (Except String) Highlighted
  | .text s => .text <$> sourceLeaf s false
  | .unparsed s => .unparsed <$> sourceLeaf s false
  | .token tok => do
    let content ← sourceLeaf tok.content true
    return .token { tok with content }
  | .point .. => pure .empty
  | .span info content => .span info <$> sourceTokens content
  | .tactics info first last content => .tactics info first last <$> sourceTokens content
  | .seq children => .seq <$> children.mapM sourceTokens

private def sourceSpelling (source : String) (hl : Highlighted) : Except String Highlighted := do
  let (result, rest) ← (sourceTokens hl).run source.toList
  unless rest.isEmpty do throw "Source extends beyond the highlighted declaration"
  unless result.toString == source do throw "Restored declaration source does not match"
  return result

#guard (sourceSpelling "operations.«public» s"
  (.seq #[.text "operations.", .token ⟨.unknown, "public"⟩, .text " s"])).toOption.map
    (·.toString) == some "operations.«public» s"
#guard (sourceSpelling "foo.«bar».baz" (.token ⟨.unknown, "foo.bar.baz"⟩)).toOption.map
    (·.toString) == some "foo.«bar».baz"
#guard match sourceSpelling "wrong" (.token ⟨.unknown, "right"⟩) with
  | .error _ => true
  | .ok _ => false

/-- Locate the declaration's first top-level `:=`, `where`, or equation bar.
Ignore comments, strings, and nested binders so binder defaults do not split a signature. -/
private def boundaries (source : String) : Nat × Option Nat × Option Nat := Id.run do
  let chars := source.toList.toArray
  let mut depth := 0
  let mut comments := 0
  let mut lineComment := false
  let mut quoted := false
  let mut escaped := false
  let mut skipNext := false
  let mut atLineStart := true
  let mut firstCommentIsDoc := false
  let mut docEnd := 0
  for i in [:chars.size] do
    if skipNext then
      skipNext := false
      continue
    let c := chars[i]!
    let next := chars[i + 1]?.getD '\x00'
    if comments > 0 then
      if c == '/' && next == '-' then
        comments := comments + 1
        skipNext := true
      else if c == '-' && next == '/' then
        comments := comments - 1
        skipNext := true
        if comments == 0 && firstCommentIsDoc then
          docEnd := i + 2
          firstCommentIsDoc := false
      continue
    if lineComment then
      if c == '\n' then
        lineComment := false
        atLineStart := true
      continue
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
      continue
    if c == '/' && next == '-' then
      firstCommentIsDoc := docEnd == 0 && atLineStart && chars[i + 2]?.getD '\x00' == '-'
      comments := 1
      skipNext := true
      continue
    if c == '-' && next == '-' then
      lineComment := true
      skipNext := true
      continue
    if c == '"' then
      quoted := true
      atLineStart := false
      continue
    if c == '(' || c == '[' || c == '{' then depth := depth + 1
    else if c == ')' || c == ']' || c == '}' then depth := depth - 1
    if depth == 0 then
      if c == ':' && next == '=' then return (docEnd, some i, some (i + 2))
      if c == '|' && atLineStart then return (docEnd, some i, some i)
      if c == 'w' && chars[i + 1]?.getD '\x00' == 'h' &&
          chars[i + 2]?.getD '\x00' == 'e' && chars[i + 3]?.getD '\x00' == 'r' &&
          chars[i + 4]?.getD '\x00' == 'e' &&
          (i == 0 || (chars[i - 1]!).isWhitespace) &&
          (chars[i + 5]?.getD ' ').isWhitespace then
        return (docEnd, some i, some i)
    if c == '\n' then atLineStart := true
    else if !c.isWhitespace then atLineStart := false
  return (docEnd, none, none)

private def boundaryCheck : Bool := Id.run do
  let source := "/-- x := ignored -/\ndef f (x : Nat := 1) : Nat := by\n  exact x"
  let (docEnd, signatureEnd?, bodyStart?) := boundaries source
  let some signatureEnd := signatureEnd? | return false
  let some bodyStart := bodyStart? | return false
  let (_, eqSig?, eqBody?) := boundaries "def f : Nat → Nat\n| 0 => 0\n| n + 1 => n"
  let (_, whereSig?, whereBody?) := boundaries "structure S where\n  field : Nat"
  return docEnd > 0 &&
    (SubVerso.Compat.String.drop source signatureEnd).startsWith ":= by" &&
    (SubVerso.Compat.String.drop source bodyStart).startsWith " by" &&
    eqSig? == eqBody? && eqSig?.isSome &&
    whereSig? == whereBody? && whereSig?.isSome

#guard boundaryCheck

private def declarationWindow (env : Environment) (name : Name) (part : String)
    (docstrings : Bool) (hl : Highlighted) : Except String Highlighted := do
  let source := hl.toString
  let (docEnd, signatureEnd?, bodyStart?) := boundaries source
  let start := if docstrings then 0 else docEnd
  let (first, last) ← match part with
    | "full" => pure (start, source.length)
    | "signature" => pure (start, signatureEnd?.getD source.length)
    | "body" | "proof" =>
        let some bodyStart := bodyStart?
          | throw s!"{name} has no declaration body"
        if part == "proof" && !(env.find? name |>.any fun c => c matches .thmInfo _) then
          throw s!"{name} is not a theorem; use (part := \"body\")"
        pure (bodyStart, source.length)
    | other => throw s!"Unknown part '{other}'; expected full, signature, body, or proof"
  let selected := SubVerso.Compat.String.take
    (SubVerso.Compat.String.drop source first) (last - first)
  let leftTrim := (selected.takeWhile Char.isWhitespace).toString.length
  let trimmed := selected.trimAscii.toString
  if trimmed.isEmpty then throw s!"No {part} source found for {name}"
  let beginAt := first + leftTrim
  let result := window hl beginAt (beginAt + trimmed.length)
  unless result.toString == trimmed do
    throw s!"Highlighted source range mismatch for {name} ({part})"
  return result

private def declarationCardCss : String := r#"
.bp_declaration_card {
  min-width: 0;
  margin: 1rem 0 0.4rem;
  border: 1px solid var(--bp-color-border);
  border-radius: 0.7rem;
  background: var(--bp-color-surface);
  overflow: hidden;
}
.bp_declaration_card > summary {
  display: flex;
  align-items: center;
  gap: 0.6rem;
  flex-wrap: wrap;
  padding: 0.65rem 0.85rem;
  cursor: pointer;
  list-style: none;
  background: var(--bp-color-surface-muted);
  color: var(--bp-color-text-strong);
}
.bp_declaration_card > summary::-webkit-details-marker { display: none; }
.bp_declaration_card > summary::after {
  content: "";
  width: 0.45rem;
  height: 0.45rem;
  margin-left: auto;
  border-right: 2px solid currentColor;
  border-bottom: 2px solid currentColor;
  transform: rotate(-45deg);
}
.bp_declaration_card[open] > summary {
  border-bottom: 1px solid var(--bp-color-border);
}
.bp_declaration_card[open] > summary::after { transform: rotate(45deg); }
.bp_declaration_card > summary:focus-visible {
  outline: 2px solid var(--bp-color-accent-info);
  outline-offset: -2px;
}
.bp_declaration_card_pill {
  padding: 0.18rem 0.6rem;
  border: 1px solid var(--bp-color-accent-info);
  border-radius: 999px;
  color: var(--bp-color-accent-info);
  font-weight: 600;
  font-size: 0.8rem;
}
.bp_declaration_card_name {
  font-weight: 600;
  overflow-wrap: anywhere;
}
.bp_declaration_card_hint {
  color: var(--bp-color-text-muted);
  font-size: 0.8rem;
}
.bp_declaration_card_body {
  min-width: 0;
  padding: 0.9rem 1rem;
}
.bp_declaration_card_body > code.hl.lean.block {
  max-width: 100%;
  overflow-x: auto;
  white-space: pre;
  line-height: 1.5;
  font-size: 0.9rem;
}
/* Text labels carry provenance; colour provides a redundant visual cue. */
.bp_declaration_card[data-provenance="VCVio"] .bp_declaration_card_pill {
  background: #dbeafe; color: #1e40af;
}
.bp_declaration_card[data-provenance="cslib"] .bp_declaration_card_pill {
  background: #dcfce7; color: #166534;
}
.bp_declaration_card[data-provenance="UAKE framework"] .bp_declaration_card_pill {
  background: #ede9fe; color: #5b21b6;
}
.bp_declaration_card[data-provenance="PQXDH model"] .bp_declaration_card_pill {
  background: #fef3c7; color: #92400e;
}
/* Keep Blueprint's heading status but hide its duplicate signature panel. */
.bp_wrapper:has(> .bp_content .bp_declaration_card) + .bp_code_panel_wrapper {
  display: none;
}
@media (max-width: 640px) {
  .bp_declaration_card > summary { padding: 0.55rem 0.65rem; }
  .bp_declaration_card_body { padding: 0.65rem; }
}
"#

block_extension Block.declarationCard (name part sourcePath : String) where
  data := toJson (name, part, sourcePath)
  traverse _ _ _ := pure none
  extraCss := [declarationCardCss]
  toTeX := none
  toHtml := some <| fun _ goB _ data blocks => do
    let (name, part, sourcePath) := (fromJson? (α := String × String × String) data).toOption.getD ("", "full", "")
    let shortName := (name.splitOn ".").getLast!
    let view := if part == "full" then "source" else part
    let provenance := if (sourcePath.splitOn "/VCV-io/").length > 1 then "VCVio"
      else if (sourcePath.splitOn "/cslib/").length > 1 then "cslib"
      else if (sourcePath.splitOn "/Protocols/ToVCVio/").length > 1 then "UAKE framework"
      else if (sourcePath.splitOn "/Protocols/Models/").length > 1 then "PQXDH model"
      else "libsignal-verify"
    let code ← blocks.mapM goB
    pure <| tag "details" #[("class", "bp_declaration_card"), ("open", ""), ("data-provenance", provenance)]
      (.seq #[
        tag "summary" #[("title", name)] (.seq #[
          tag "span" #[("class", "bp_declaration_card_pill")] (.text true provenance),
          tag "code" #[("class", "bp_declaration_card_name")] (.text true shortName),
          tag "span" #[("class", "bp_declaration_card_hint")]
            (.text true s!"{view} · hover names for types")
        ]),
        tag "div" #[("class", "bp_declaration_card_body")] (.seq code),
        tag "a" #[("class", "bp_source_link"), ("href", sourcePath), ("data-declaration", name)]
          (.text true "Source file")
      ])

/-- Native Verso code block for an imported declaration, without source markers
or a hand-copied excerpt. Use `(lean := "...")` on the enclosing Blueprint node
for its compiled status and cross-references. -/
@[code_block]
def declaration : CodeBlockExpanderOf DeclarationConfig
  | cfg, contents => do
    unless contents.getString.trimAscii.isEmpty do
      throwErrorAt contents "Leave this block empty; its code comes from the imported declaration"
    let env ← getEnv
    let some idx := env.getModuleIdxFor? cfg.name
      | throwError "Import the module that defines {cfg.name}"
    let modName := env.header.moduleNames[idx.toNat]!
    let items ← loadModuleContent (Syntax.mkStrLit ".") modName.toString
    let hits := items.filter (·.defines.contains cfg.name)
    unless hits.size == 1 do
      throwError "Expected one highlighted command for {cfg.name} in {modName}, found {hits.size}"
    let some (originalPath, sourcePath) := moduleSource modName.toString
      | throwError "{cfg.name}: only VCVio, cslib and Protocols declarations have source links"
    let original ← IO.FS.readFile (System.FilePath.mk originalPath)
    let normalized := hits[0]!.code.toString
    let code ← if (original.splitOn normalized.trimAscii.toString).length > 1 then
      pure hits[0]!.code
    else do
      let some (first, last) := hits[0]!.range
        | throwError "No original source range for {cfg.name}"
      let positions := FileMap.ofString original
      let source := (SubVerso.Compat.String.Pos.extract original
        (positions.ofPosition first) (positions.ofPosition last)).trimAscii.toString
      let leftTrim := (normalized.takeWhile Char.isWhitespace).toString.length
      let trimmed := normalized.trimAscii.toString
      let code := window hits[0]!.code leftTrim (leftTrim + trimmed.length)
      match sourceSpelling source code with
      | .ok code => pure code
      | .error reason => throwError
          "{cfg.name}: {reason}\nOriginal command: {repr source}\nHighlighted command: {repr code.toString}"
    let hl ← match declarationWindow env cfg.name cfg.part cfg.docstrings code with
      | .ok hl => pure hl
      | .error reason => throwError "{reason}"
    let source ← ``(ExternalCode.leanBlock (genre := Verso.Genre.Manual)
      $(quote hl) $(quote ({} : CodeConfig)))
    ``(Verso.Doc.Block.other
      (Block.declarationCard $(quote cfg.name.toString) $(quote cfg.part) $(quote sourcePath)) #[$source])

private def mathCodeCss : String := r#"
.content-wrapper p > code:not(.bp_math) { overflow-wrap: anywhere; white-space: normal; }
.content-wrapper:has(.bp_math_code) { max-width: 90rem; }
.content-wrapper:has(.bp_math_code) > section { max-width: none; }
.content-wrapper:has(.bp_math_code) > section > p { max-width: 75ch; }
.bp_math_code {
  display: grid;
  grid-template-columns: minmax(18rem, 0.85fr) minmax(0, 1.15fr);
  gap: 1.5rem;
  align-items: start;
}
.bp_math_code > div { min-width: 0; }
.bp_math_code .bp_declaration_card { margin-top: 0; }
.bp_math_code .bp_pair_prose,
.bp_math_code .bp_pair_prose p,
.bp_math_code .bp_pair_prose li {
  font-family: Georgia, "Times New Roman", serif;
  line-height: 1.7;
}
.bp_math_code .bp_declaration_card_body > code.hl.lean.block {
  white-space: pre-wrap;
  overflow-wrap: anywhere;
}
.bp_math_code .katex-display { overflow-x: auto; overflow-y: hidden; padding: 0.2rem 0; }
@media (max-width: 1050px) {
  .bp_math_code { grid-template-columns: minmax(0, 1fr); }
  .bp_math_code .bp_pair_prose { order: -1; }
}
"#

block_extension Block.mathCode where
  traverse _ _ _ := pure none
  extraCss := [mathCodeCss]
  toTeX := none
  toHtml := some <| fun _ goB _ _ blocks => do
    let some source := blocks[0]?
      | Verso.reportError "A math/code pair requires a source block" *> pure .empty
    let code ← goB source
    let prose ← (blocks.drop 1).mapM goB
    pure <| tag "div" #[("class", "bp_math_code")] (.seq #[
      tag "div" #[("class", "bp_pair_prose")] (.seq prose),
      tag "div" #[("class", "bp_source")] code])

/-- Pair mathematical prose with imported source, retaining declaration view options. -/
@[directive]
def pair : DirectiveExpanderOf DeclarationConfig
  | cfg, contents => do
    let source ← declaration cfg (Syntax.mkStrLit "")
    let prose ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other Block.mathCode #[ $source, $[$prose],* ])

end LibsignalVerifyBlueprint
