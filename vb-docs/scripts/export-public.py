#!/usr/bin/env python3
"""Copy the rendered book to a publication folder and remove every local path from the copy.

`lake exe vbp build` writes the absolute path of the build directory into some of its files
(`xref.json`, `-verso-data/blueprint-manifest.json` and the data embedded in `find/index.html`).
This script copies `_out/site/html-multi` to a new folder, rewrites each such path to a path
relative to the repository root, and fails when a path under `/Users/` or `/home/` remains.
It also fails when a link to the source of this repository names a commit other than the
expected one, so a book that was compiled for one commit cannot be published for another.

Run it from any directory:

    python3 vb-docs/scripts/export-public.py --destination _site [--source-revision COMMIT]
"""
import argparse
import re
import shutil
import sys
from pathlib import Path

BOOK = Path(__file__).resolve().parents[1]
REPOSITORY = BOOK.parent
SOURCE_LINK = re.compile(rb'libsignal-verify/blob/([0-9A-Za-z{}]+)/')
# A local path in plain, JSON-escaped (`\/`) or percent-encoded form.
LOCAL_PATH = re.compile(rb'(?:/|\\/|%2[Ff])(?:Users|home)(?:/|\\/|%2[Ff])')
TEXT_SUFFIXES = {'.html', '.json', '.js', '.mjs', '.css', '.txt', '.md', '.svg', '.map', '.xml'}


def build_roots() -> list[Path]:
    """The directories whose absolute paths the build may have written: longest first."""
    roots = {REPOSITORY, Path.home()}
    roots |= {root.resolve() for root in roots}
    return sorted(roots, key=lambda root: len(str(root)), reverse=True)


def relativise(text: str, roots: list[Path]) -> str:
    """Turn an absolute path under the repository into a path relative to the repository root.
    A path under the home directory but outside the repository loses its home prefix."""
    for root in roots:
        for spelling, slash in ((str(root), '/'), (str(root).replace('/', '\\/'), '\\/')):
            # `root/rest` becomes `rest`; a bare `root` becomes `.`
            text = text.replace(spelling + slash, '')
            text = re.sub(re.escape(spelling) + r'(?![\w.-])', '.', text)
    return text


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('--source', type=Path, default=BOOK / '_out/site/html-multi',
                        help='rendered book (default: vb-docs/_out/site/html-multi)')
    parser.add_argument('--destination', type=Path, default=BOOK / '_out/site/public',
                        help='publication folder, replaced if it exists (default: vb-docs/_out/site/public)')
    parser.add_argument('--source-revision',
                        help='commit that the source links must name (default: the file vb-docs/source-revision)')
    args = parser.parse_args()

    source, destination = args.source.resolve(), args.destination.resolve()
    if not (source / 'index.html').is_file():
        sys.exit(f'{source}/index.html does not exist: build the book with `lake exe vbp build` first')
    if destination == source or source in destination.parents or destination in source.parents:
        sys.exit('the destination must be a folder of its own, outside the rendered book')

    expected = args.source_revision
    if expected is None and (BOOK / 'source-revision').is_file():
        expected = (BOOK / 'source-revision').read_text().strip()
    if expected is not None and not re.fullmatch(r'[0-9a-f]{40}', expected):
        sys.exit(f'not a 40-digit lowercase hexadecimal commit hash: {expected!r}')

    shutil.rmtree(destination, ignore_errors=True)
    shutil.copytree(source, destination, symlinks=False)

    roots = build_roots()
    revisions: set[str] = set()
    rewritten, problems = 0, []
    for path in sorted(destination.rglob('*')):
        if path.is_symlink():
            problems.append(f'{path.relative_to(destination)}: symbolic link')
            continue
        if not path.is_file():
            continue
        data = path.read_bytes()
        if path.suffix.lower() in TEXT_SUFFIXES:
            text = data.decode('utf-8')
            clean = relativise(text, roots)
            if clean != text:
                path.write_text(clean, encoding='utf-8')
                rewritten += 1
            data = clean.encode('utf-8')
        revisions |= {m.group(1).decode() for m in SOURCE_LINK.finditer(data)}
        for match in LOCAL_PATH.finditer(data):
            around = data[max(0, match.start() - 40):match.end() + 40].decode('utf-8', 'replace')
            problems.append(f'{path.relative_to(destination)}: local path remains near {around!r}')
            break
        if b'{revision}' in data:
            problems.append(f'{path.relative_to(destination)}: unresolved {{revision}} placeholder')

    wanted = {expected} if expected is not None else revisions
    if revisions != wanted or len(revisions) > 1:
        problems.append(f'links to the source name the commits {sorted(revisions)}; expected {sorted(wanted)}')
    if not revisions:
        problems.append('no link to the source of the repository found: did the book lose its source links?')

    if problems:
        shutil.rmtree(destination, ignore_errors=True)
        print('export failed:', *problems, sep='\n  ', file=sys.stderr)
        return 1

    (destination / '.nojekyll').write_text('')
    print(f'exported {destination}: {rewritten} files rewritten, source links name {sorted(revisions)[0]}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
