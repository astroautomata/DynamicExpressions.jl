#!/usr/bin/env python3
"""Check or refresh the Julia source hashes for the Lean property registry."""
import argparse
import re
from collections import defaultdict
from hashlib import sha256
from pathlib import Path

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parents[1]
HASHES = LEAN / 'source-hashes.tsv'
UPDATE = 'test/lean/scripts/source-hashes.py update'


def rows(table, columns, path_column):
    with table.open(encoding='utf-8') as source:
        for number, line in enumerate(source, 1):
            if line.startswith(('#', '\n')):
                continue
            fields = line.rstrip('\n').split('\t')
            if len(fields) != columns or not fields[0] or not fields[path_column]:
                raise SystemExit(f'{table.name}:{number}: malformed TSV row')
            path = Path(fields[path_column])
            if path.is_absolute() or '..' in path.parts:
                raise SystemExit(f'{table.name}:{number}: expected a repository-relative path')
            yield number, fields


def digest(path):
    return sha256((ROOT / path).read_bytes()).hexdigest()


def read_hashes():
    hashes = {}
    for number, (path, checksum) in rows(HASHES, 2, 0):
        if path in hashes or not re.fullmatch(r'[0-9a-fA-F]{64}', checksum):
            raise SystemExit(f'{HASHES.name}:{number}: duplicate path or invalid SHA-256')
        hashes[path] = checksum.lower()
    return hashes


def warn(path, reason, ids):
    examples = ', '.join(ids[:5]) + ('...' if len(ids) > 5 else '')
    citations = f'{len(ids)} properties cite it' + (f' ({examples})' if ids else '')
    message = f'{path} {reason}; {citations}. Update test/lean and run {UPDATE}.'
    file = path.replace('%', '%25').replace(',', '%2C').replace(':', '%3A')
    print(f'::warning file={file},title=Lean model may be stale::{message.replace("%", "%25")}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', nargs='?', choices=('check', 'update'), default='check')
    mode = parser.parse_args().mode
    properties = defaultdict(list)
    for _, fields in rows(LEAN / 'registry.tsv', 7, 4):
        properties[fields[4]].append(fields[0])

    if mode == 'update':
        entries = ''.join(f'{path}\t{digest(path)}\n' for path in sorted(properties))
        HASHES.write_text(f'# Regenerate with {UPDATE}\n{entries}', encoding='utf-8', newline='\n')
        return

    hashes = read_hashes() if HASHES.exists() else {}
    stale = 0
    for path in sorted(hashes.keys() | properties.keys()):
        if path not in hashes:
            reason = 'has no recorded hash in test/lean/source-hashes.tsv'
        elif not (ROOT / path).is_file() or digest(path) != hashes[path]:
            reason = 'changed since the Lean model last matched it'
        else:
            continue
        warn(path, reason, properties.get(path, []))
        stale += 1
    print(f'SOURCE HASHES {stale} stale' if stale else 'SOURCE HASHES ok')


if __name__ == '__main__':
    main()
