#!/usr/bin/env python3
"""Check Protocols/LEDGER.md against the output of its "How to regenerate" commands.

Usage, from the repository root after `lake build`:

    rg -n -g '*.lean' "$PATTERN" \
        Protocols Protocols.lean ProtocolsTest ProtocolsTest.lean > admissions.log
    lake env lean scripts/Ledger.lean > closures.log
    python3 scripts/ledger-check.py closures.log admissions.log

where `$PATTERN` is the pattern in the "How to regenerate" section of LEDGER.md and in the `rg`
step of `.github/workflows/lean.yml`, the same as `SORRY|TRUST` below.

Exits 0 iff every closure, count and pin that the LEDGER records matches the regenerated output.
It reads three shapes from LEDGER.md:

- three-column table rows `| `Decl`, `short`, ... | `File` | `ax`, ... or none |`, where a short
  name extends the namespace of the first name in the row; axioms are compared as a set;
- a line `` `Decl`: `` followed by a fenced block listing the axioms, compared in order;
- the two-column State table: the three admission counts and the Lean, Mathlib, VCVio and Aeneas
  pins, checked against the `rg` listing, `lean-toolchain` and `lake-manifest.json`.

The counts match whole tokens: `sorry` as a word, so that `sorryAx` in a recorded axiom list does
not count, and `axiom` only as a declaration keyword at the start of a line, after optional
attributes and modifiers, so that `#print axioms` in a spec summary does not count.

Every declaration printed by `scripts/Ledger.lean` must be recorded, and every recorded one printed.
"""
import json
import re
import sys
from pathlib import Path
from typing import Callable


SORRY = re.compile(r'\bsorry\b')
TRUST = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*'
                   r'(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*'
                   r'axiom\b|native_decide|set_option')


def count(lines: list[str], pred: Callable[[str, str], bool]) -> int:
    """Count `rg -n` lines `file:line:text` for which `pred(file, text)` holds."""
    return sum(1 for l in lines if pred(l.split(':', 2)[0], l.split(':', 2)[2]))


root = Path(__file__).resolve().parent.parent
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
    '`sorry` under `Protocols/`':
        count(admissions, lambda f, t: f.startswith('Protocols/') and SORRY.search(t) is not None),
    '`sorry` under `ProtocolsTest/`':
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
