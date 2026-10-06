#!/usr/bin/env python3
"""Replay the complete project and audit every authored declaration.

Requires Python 3, Git, Lake, Lean 4.19.0, and the nine manifest-pinned packages.
Run from any directory: python3 /path/to/this/project/verify.py
No external mathematical computation is used: all mathematics is kernel-checked
by Lean. This script checks build status, source inventory, and axiom provenance.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
LOGS = ROOT / 'verification-logs'
LOGS.mkdir(exist_ok=True)
EXPECTED_REVISIONS = {
    'mathlib': 'c44e0c8ee63ca166450922a373c7409c5d26b00b',
    'plausible': '77e08eddc486491d7b9e470926b3dbe50319451a',
    'LeanSearchClient': '25078369972d295301f5a1e53c3e5850cf6d9d4c',
    'importGraph': 'e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b',
    'proofwidgets': 'c4919189477c3221e6a204008998b0d724f49904',
    'aesop': '5d50b08dedd7d69b3d9b3176e0d58a23af228884',
    'Qq': 'fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02',
    'batteries': 'f5d04a9c4973d401c8c92500711518f7c656f034',
    'Cli': '02dbd02bc00ec4916e99b04b2245b30200e200d0',
}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
records = []


def run(argv):
    result = subprocess.run(argv, cwd=ROOT, text=True, capture_output=True)
    record = {'argv': argv, 'cwd': str(ROOT), 'exitcode': result.returncode,
              'stdout': result.stdout, 'stderr': result.stderr}
    records.append(record)
    (LOGS / f'{len(records):02d}.json').write_text(json.dumps(record, indent=2) + '\n')
    print(f'[{len(records):02d}] exit {result.returncode}: ' + ' '.join(argv))
    if result.returncode != 0:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise RuntimeError('Command failed with the recorded true exit code.')
    return result.stdout


def main():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    revisions = {p['name']: p['rev'] for p in manifest['packages']}
    assert revisions == EXPECTED_REVISIONS
    for name, expected in EXPECTED_REVISIONS.items():
        package = str(ROOT / '.lake' / 'packages' / name)
        assert run(['git', '-C', package, 'rev-parse', 'HEAD']).strip() == expected
        assert run(['git', '-C', package, 'status', '--porcelain', '--untracked-files=no']) == ''
    assert 'version 4.19.0' in run(['lake', 'env', 'lean', '--version'])
    source = (ROOT / 'Conjecture637.lean').read_text()
    pattern = r'^(def|abbrev|theorem|lemma|instance)\s+([A-Za-z_][A-Za-z_0-9]*)'
    declarations = [{'kind': m.group(1), 'name': 'Conjecture637.' + m.group(2),
                     'line': source.count('\n', 0, m.start()) + 1}
                    for m in re.finditer(pattern, source, re.MULTILINE)]
    assert declarations == json.loads((ROOT / 'declarations.json').read_text())
    names = {d['name'] for d in declarations}
    assert len(names) == len(declarations) == 36
    for filename in ['Conjecture637.lean', 'Audit.lean']:
        text = (ROOT / filename).read_text()
        assert not re.search(r'\b(sorry|admit|native_decide|unsafe|implemented_by)\b', text)
        assert not re.search(r'^\s*(axiom|constant|opaque)\s', text, re.MULTILINE)
    run(['lake', 'build'])
    run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Conjecture637.lean'])
    output = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'])
    axiom_sets = {}
    for name, contents in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        axiom_sets[name] = set(contents.split(', ')) if contents else set()
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        axiom_sets[name] = set()
    assert set(axiom_sets) == names
    assert all(axioms <= ALLOWED_AXIOMS for axioms in axiom_sets.values())
    result = {
        'passed': True,
        'handwritten_declarations': len(declarations),
        'dependency_revisions': revisions,
        'all_dependency_tracked_trees_clean': True,
        'axioms': {name: sorted(axioms) for name, axioms in sorted(axiom_sets.items())},
        'command_exitcodes': [record['exitcode'] for record in records],
        'source_sha256': {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                          for name in ['Conjecture637.lean', 'Audit.lean', 'lakefile.toml',
                                       'lake-manifest.json', 'lean-toolchain',
                                       'declarations.json', 'verify.py']},
        'scope': 'Necessary n=3 center conjunct is false; conjunction false for arbitrary second proposition.',
    }
    (ROOT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: complete build, strict replay, all 36 axiom checks, all nine exact dependency pins.')


if __name__ == '__main__':
    main()
