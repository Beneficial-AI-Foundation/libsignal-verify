#!/usr/bin/env python3
"""Check Protocols/LEDGER.md against the output of its "How to regenerate" commands.

Usage, from the repository root after `lake build`:

    rg -n -g '*.lean' 'sorry|axiom|native_decide|set_option' \
        Protocols Protocols.lean ProtocolsTest ProtocolsTest.lean > admissions.log
    lake env lean scripts/Ledger.lean > closures.log
    python3 scripts/ledger-check.py closures.log admissions.log

Exits 0 iff every closure, count and pin that the LEDGER records matches the regenerated output.
It reads three shapes from LEDGER.md:

- three-column table rows `| `Decl`, `short`, ... | `File` | `ax`, ... or none |`, where a short
  name extends the namespace of the first name in the row; axioms are compared as a set;
- a line `` `Decl`: `` followed by a fenced block listing the axioms, compared in order;
- the two-column State table: the three admission counts and the Lean, Mathlib, VCVio and Aeneas
  pins, checked against the `rg` listing, `lean-toolchain` and `lake-manifest.json`.

The `rg` pattern only selects candidate lines. A listed line counts as an admission when its
executable text, what is left of it once `code_lines` blanks the comments of its file, contains
`sorry` or `sorryAx` as a word, `axiom` as the declaration keyword at the start of the line (after
optional attributes and modifiers), or `native_decide` or `set_option` as a word. An explicit
`sorryAx` term therefore counts, while the `sorryAx` in an axiom list recorded as the expected
output of `#guard_msgs`, which is a doc comment, does not, and `#print axioms` is no declaration.
`python3 scripts/ledger-check.py --self-test` checks the comment scanner on fixed cases.

Every declaration printed by `scripts/Ledger.lean` must be recorded, and every recorded one printed.
"""
import json
import re
import sys
from pathlib import Path
from typing import Callable


SORRY = re.compile(r'\bsorry(?:Ax)?\b')
TRUST = re.compile(r'^\s*(?:@\[(?:[^\[\]]|\[[^\]]*\])*\]\s*)*'
                   r'(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*'
                   r'axiom\b|\bnative_decide\b|\bset_option\b')
COMMENT_MARK = re.compile(r'/-|-/')
RAW = re.compile(r'r(#*)"')
CHAR = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")


def ident_char(c: str) -> bool:
    """Whether `c` can end a Lean identifier, so that a `'` or `r` after it belongs to the name."""
    return c.isalnum() or c in "_'!?"


def code_lines(src: str) -> list[str]:
    """The lines of the Lean source `src` with every comment blanked.

    Line comments and nested block comments, which include docstrings and the expected output of
    `#guard_msgs`, become spaces, and line breaks stay, so line numbers do not move. String, raw
    string and character literals and quoted identifiers `«…»` are kept: a comment marker inside
    one opens no comment, and a token inside one still counts, which errs towards counting. As in
    Lean, a quoted identifier runs to the next `»`.
    """
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        c, prev = src[i], (src[i - 1] if i else ' ')
        keep = True
        if depth:
            keep = False
            mark = COMMENT_MARK.search(src, i)
            if mark is None:
                j = n
            elif mark.start() > i:
                j = mark.start()
            else:
                depth += 1 if c == '/' else -1
                j = i + 2
        elif src.startswith('/-', i):
            depth, j, keep = 1, i + 2, False
        elif src.startswith('--', i):
            j, keep = src.find('\n', i), False
            if j < 0:
                j = n
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            j = min(j + 1, n)
        elif c == '«':
            j = src.find('»', i + 1)
            j = n if j < 0 else j + 1
        else:
            raw = RAW.match(src, i) if c == 'r' and not ident_char(prev) else None
            char = CHAR.match(src, i) if c == "'" and not ident_char(prev) else None
            if raw is not None:
                end = src.find('"' + raw.group(1), raw.end())
                j = n if end < 0 else end + 1 + len(raw.group(1))
            elif char is not None:
                j = char.end()
            else:
                j = i + 1
        out.append(src[i:j] if keep else re.sub(r'[^\n]', ' ', src[i:j]))
        i = j
    return ''.join(out).split('\n')


# Regression cases for `code_lines`, one per line. Lines 7, 9, 11, 13, 15 and 16 hold an admission
# that a comment marker inside a literal or a quoted identifier must not hide. Line 17 is a comment
# that a quote inside the identifier of line 16 must not turn into code. Lines 19 and 20 hold
# `axiom` declarations. Every other line names the tokens only in a comment or a command.
SELF_TEST = r"""/-- info: 'X' depends on axioms: [propext, sorryAx, Classical.choice] -/
#guard_msgs in
#print axioms X
-- a line comment naming sorry, sorryAx, native_decide and set_option
/- outer /- nested sorryAx -/ still inside: sorry
axiom inside_block : False -/
theorem unchecked : False := sorryAx False false
def s : String := "/-"
theorem after_string : False := sorryAx False false
def r1 : String := r#"/- -- "#
theorem after_raw : False := sorryAx False false
def c : Char := '"'
theorem after_char : False := sorry -- trailing comment with sorryAx
def «/-» : Nat := 0
theorem after_quoted : False := sorryAx False false
def «"' --» : Nat := sorry
-- a comment after the quoted identifier: sorry
theorem h' : True := trivial -- after a primed name: sorry
private axiom hidden : False
@[simp, aesop safe [foo]] noncomputable axiom attributed : Nat
/-! module doc mentioning axiom foo : False and native_decide -/
"""
SELF_TEST_SORRY = {7, 9, 11, 13, 15, 16}
SELF_TEST_TRUST = {19, 20}


def self_test() -> bool:
    """Check `code_lines`, `SORRY` and `TRUST` on `SELF_TEST`, and print any mismatch."""
    lines = code_lines(SELF_TEST)
    sorry = {i for i, l in enumerate(lines, 1) if SORRY.search(l)}
    trust = {i for i, l in enumerate(lines, 1) if TRUST.search(l)}
    if sorry != SELF_TEST_SORRY or trust != SELF_TEST_TRUST:
        print(f'SELF-TEST FAILED: sorry lines {sorted(sorry)}, axiom lines {sorted(trust)}')
        return False
    print('SELF-TEST OK')
    return True


if sys.argv[1:] == ['--self-test']:
    sys.exit(0 if self_test() else 1)

root = Path(__file__).resolve().parent.parent
code_of: dict[str, list[str]] = {}


def code(entry: str) -> tuple[str, str]:
    """The file of an `rg -n` line `file:line:text` and the executable text of that line."""
    file, line, _ = entry.split(':', 2)
    if file not in code_of:
        code_of[file] = code_lines((root / file).read_text())
    return file, code_of[file][int(line) - 1]


def count(lines: list[str], pred: Callable[[str, str], bool]) -> int:
    """Count the listed lines whose file and executable text satisfy `pred`."""
    return sum(1 for l in lines if pred(*code(l)))


probe = Path(sys.argv[1]).read_text()
admissions = [l for l in Path(sys.argv[2]).read_text().splitlines() if l.strip()]
ledger = (root / 'Protocols/LEDGER.md').read_text()

# `#print axioms` output: name -> axioms in printed order.
regen: dict[str, list[str]] = {}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", probe):
    regen[m.group(1)] = [a.strip() for a in (m.group(2) or '').split(',') if a.strip()]

recorded: dict[str, tuple[list[str], bool]] = {}  # name -> (axioms, compared in order?)
for line in ledger.splitlines():
    cells = [c.strip() for c in line.strip().strip('|').split('|')]
    if len(cells) != 3 or not cells[0].startswith('`'):
        continue
    names = re.findall(r'`([^`]+)`', cells[0])
    if '.' not in names[0]:
        continue
    prefix = names[0].rsplit('.', 1)[0]
    axioms = [] if cells[2] == 'none' else re.findall(r'`([^`]+)`', cells[2])
    for n in names:
        recorded[n if '.' in n else f'{prefix}.{n}'] = (axioms, False)
for m in re.finditer(r'^`([^`]+)`:\n\n```\n(.*?)\n```', ledger, re.M | re.S):
    recorded[m.group(1)] = ([a.strip() for a in m.group(2).split(',')], True)

ok = bool(regen) and bool(recorded)
print('== Closures ==')
for name, axioms in regen.items():
    if name not in recorded:
        ok = False
        print(f'MISSING-IN-LEDGER {name}: {axioms}')
        continue
    rec, ordered = recorded[name]
    same = rec == axioms if ordered else sorted(rec) == sorted(axioms)
    ok &= same
    print(f"{'MATCH' if same else 'DIFF '} {name}" + ('' if same else f'\n   ledger: {rec}\n   regen:  {axioms}'))
for name in recorded.keys() - regen.keys():
    ok = False
    print(f'MISSING-IN-PROBE {name}')

print('== State table ==')
pkgs = {p['name']: p for p in json.loads((root / 'lake-manifest.json').read_text())['packages']}
toolchain = (root / 'lean-toolchain').read_text().strip()
state = dict(re.findall(r'^\| (.+?) \| (.+?) \|$', ledger, re.M))
observed = {
    '`sorry` or `sorryAx` under `Protocols/`':
        count(admissions, lambda f, t: f.startswith('Protocols/') and SORRY.search(t) is not None),
    '`sorry` or `sorryAx` under `ProtocolsTest/`':
        count(admissions, lambda f, t: f.startswith('ProtocolsTest/') and SORRY.search(t) is not None),
    '`axiom`, `native_decide`, `set_option` under `Protocols/` and `ProtocolsTest/`':
        count(admissions, lambda f, t: TRUST.search(t) is not None),
    'Lean': toolchain.split(':')[1],
    'Mathlib': f"{pkgs['mathlib']['rev'][:8]} ({pkgs['mathlib']['inputRev']})",
    'VCVio': pkgs['VCVio']['rev'][:8],
    'Aeneas': pkgs['aeneas']['inputRev'],
}
for key, value in observed.items():
    same = str(value) == state.get(key)
    ok &= same
    print(f"{'MATCH' if same else 'DIFF '} {key}: ledger={state.get(key)!r} observed={str(value)!r}")

print('RESULT:', 'IDENTICAL' if ok else 'DIFFERS')
sys.exit(0 if ok else 1)
