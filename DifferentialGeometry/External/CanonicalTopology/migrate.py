#!/usr/bin/env python3
"""Restore the pinned vendor snapshot and reconcile its declaration-level migration.

With --check (the default), verify the recorded vendor source and native extensions.
With --apply, migrate only the recorded pre-migration hashes, or refresh an already
migrated checkout. The archive, map and patches are the complete migration inputs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile


def sha(data):
    return hashlib.sha256(data).hexdigest()


def transform_lean(text, mapper):
    out = []
    start = i = 0
    while i < len(text):
        if text.startswith('--', i) or text.startswith('/-', i) or text[i] == '"':
            out.append(mapper(text[start:i]))
            j = i
            if text.startswith('--', i):
                k = text.find('\n', i)
                i = len(text) if k < 0 else k
            elif text.startswith('/-', i):
                depth = 1
                i += 2
                while i < len(text) and depth:
                    if text.startswith('/-', i):
                        depth += 1
                        i += 2
                    elif text.startswith('-/', i):
                        depth -= 1
                        i += 2
                    else:
                        i += 1
            else:
                i += 1
                while i < len(text):
                    if text[i] == '\\':
                        i += 2
                    elif text[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
            out.append(text[j:i])
            start = i
        else:
            i += 1
    out.append(mapper(text[start:]))
    return ''.join(out)


def remap(text):
    def code(s):
        s = re.sub(r'(?m)^import Poincare\.',
                   'import DifferentialGeometry.External.CanonicalTopology.', s)
        return re.sub(r'\bPoincare\b', 'DifferentialGeometry', s)
    return transform_lean(text, code)


def apply_patch(original, patch):
    old = original.splitlines(keepends=True)
    lines = patch.splitlines(keepends=True)
    result = []
    cursor = 0
    i = 2
    while i < len(lines):
        match = re.match(r'@@ -(\d+)(?:,(\d+))? \+\d+(?:,\d+)? @@', lines[i])
        if not match:
            raise ValueError(f'Invalid patch hunk: {lines[i]!r}')
        pos = int(match[1]) if match[2] == '0' else max(0, int(match[1]) - 1)
        if pos < cursor:
            raise ValueError('Overlapping patch hunks')
        result.extend(old[cursor:pos])
        cursor = pos
        i += 1
        while i < len(lines) and not lines[i].startswith('@@ '):
            kind, line = lines[i][0], lines[i][1:]
            if kind in ' -':
                if cursor >= len(old) or old[cursor] != line:
                    raise ValueError(f'Patch context mismatch at line {cursor + 1}')
                cursor += 1
            if kind in ' +':
                result.append(line)
            if kind not in ' +-':
                raise ValueError(f'Unsupported patch line: {lines[i]!r}')
            i += 1
    result.extend(old[cursor:])
    return ''.join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    vendor = Path(__file__).resolve().parent
    root = vendor.parents[2]
    spec = json.loads((vendor / 'SOURCE_MAP.json').read_text())
    archive_paths = {spec['archive']: spec['archive_sha256'], **spec.get('additional_archives', {})}
    for archive_name, expected in archive_paths.items():
        if sha((vendor / archive_name).read_bytes()) != expected:
            raise ValueError(f'Pinned archive hash mismatch: {archive_name}')
    archive = vendor / spec['archive']
    planned = {}
    deleted = []
    with tarfile.open(archive, 'r:gz') as tf:
        for row in spec['modules']:
            if row.get('archive'):
                with tarfile.open(vendor / row['archive'], 'r:gz') as other:
                    raw = other.extractfile(row['source']).read()
            else:
                raw = tf.extractfile(row['source']).read()
            if sha(raw) != row['source_sha256']:
                raise ValueError(f"Upstream hash mismatch: {row['source']}")
            adapted = remap(raw.decode())
            if row.get('patch'):
                adapted = apply_patch(adapted, (vendor / row['patch']).read_text())
            data = adapted.encode()
            if sha(data) != row['external_sha256']:
                raise ValueError(f"Reconciliation hash mismatch: {row['external']}")
            planned[root / row['external']] = data
            native = root / row['previous']
            if row.get('native_patch'):
                if not native.exists():
                    raise ValueError(f'Missing native extension: {native}')
                current = native.read_bytes()
                if sha(current) == row['previous_sha256']:
                    current = apply_patch(current.decode(),
                                          (vendor / row['native_patch']).read_text()).encode()
                if sha(current) != row['native_sha256']:
                    raise ValueError(f'Native extension changed: {native}')
                planned[native] = current
            elif native.exists():
                if sha(native.read_bytes()) not in [row['previous_sha256'], *row.get('intermediate_previous_sha256', [])]:
                    raise ValueError(f'Unrecognized source at old path: {native}')
                deleted.append(native)
    for row in spec['consumer_patches']:
        if row['path'] == 'DifferentialGeometry.lean':
            continue
        path = root / row['path']
        current = path.read_bytes()
        if sha(current) == row['before_sha256']:
            current = apply_patch(current.decode(), (vendor / row['patch']).read_text()).encode()
        if sha(current) != row['after_sha256']:
            raise ValueError(f'Consumer changed: {path}')
        planned[path] = current
    aggregate = root / 'DifferentialGeometry.lean'
    removed_modules = {r['previous'].removesuffix('.lean').replace('/', '.')
                       for r in spec['modules'] if not r.get('native_patch')}
    required_modules = {r['external'].removesuffix('.lean').replace('/', '.')
                        for r in spec['modules']}
    required_modules.update(r['previous'].removesuffix('.lean').replace('/', '.')
                            for r in spec['modules'] if r.get('native_patch'))
    root_lines = aggregate.read_text().splitlines()
    root_lines = [line for line in root_lines
                  if not (line.startswith('import ') and line[7:] in removed_modules)]
    present = {line[7:] for line in root_lines if line.startswith('import ')}
    root_lines.extend('import ' + m for m in sorted(required_modules - present))
    planned[aggregate] = ('\n'.join(root_lines) + '\n').encode()
    mismatches = [str(p.relative_to(root)) for p, data in planned.items()
                  if not p.exists() or p.read_bytes() != data]
    if args.apply:
        for path, data in planned.items():
            if path.exists() and path.read_bytes() == data:
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        for path in deleted:
            path.unlink()
        print(f"Restored {len(spec['modules'])} vendor modules; "
              f"updated {len(mismatches)} files; removed {len(deleted)} old implementations.")
    else:
        if mismatches or deleted:
            raise ValueError(f'Migration differs: {mismatches}; old implementations: {deleted}')
        print(f"Verified {len(spec['modules'])} vendor modules, pinned source hashes, "
              f"native splits, and {len(spec['consumer_patches'])} consumer/aggregate patches.")


if __name__ == '__main__':
    main()
