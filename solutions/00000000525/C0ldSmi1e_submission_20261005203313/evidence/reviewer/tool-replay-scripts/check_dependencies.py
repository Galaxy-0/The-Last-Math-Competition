#!/usr/bin/env python3
"""Verify the supplied manifest pins and read-only tracked Git states."""
import hashlib, json, pathlib, subprocess
base = pathlib.Path('/private/tmp/tlmc525-review/tool-replay-project')
author = pathlib.Path('/private/tmp/tlmc525-review/tool-replay-evidence')
expected = json.loads(pathlib.Path('/private/tmp/tlmc525-author-input/pinned-dependencies.json').read_text())
actual = json.loads((base / 'lake-manifest.json').read_text())
assert actual['packages'] == expected['packages']
assert len(actual['packages']) == 9
records = []
for package in actual['packages']:
    path = base / '.lake/packages' / package['name']
    record = {'name': package['name'], 'expected_rev': package['rev'], 'commands': []}
    for command in (['git', '-C', str(path), 'rev-parse', 'HEAD'], ['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no']):
        run = subprocess.run(command, text=True, capture_output=True)
        record['commands'].append({'argv': command, 'exit_code': run.returncode, 'stdout': run.stdout, 'stderr': run.stderr})
        assert run.returncode == 0
    record['pin_matches'] = record['commands'][0]['stdout'].strip() == package['rev']
    record['tracked_clean'] = not record['commands'][1]['stdout'].strip()
    records.append(record)
(author / 'dependency-verification.json').write_text(json.dumps(records, indent=2) + '\n')
assert all(r['pin_matches'] and r['tracked_clean'] for r in records)
source = pathlib.Path('/private/tmp/tlmc525-author-input/00000000525.md').read_bytes()
assert hashlib.sha256(source).hexdigest() == 'fc349594dc530f505b3470bc698707d1ab5a9fc676a9869c2c161ed6b861a702'
print('PASS: exact nine pins, all tracked dependency states clean, original conjecture hash matched.')
