"""Replay candidate-only read-only Lean inspection tools against a built project."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--project', required=True, type=Path)
p.add_argument('--auxiliary', required=True, type=Path)
p.add_argument('--output', required=True, type=Path)
p.add_argument('--lean-bin', required=True, type=Path)
a = p.parse_args()
project, auxiliary, out, binpath = (x.resolve() for x in
    (a.project, a.auxiliary, a.output, a.lean_bin))
assert not out.exists(), 'Use a fresh output directory'
out.mkdir()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
inputs = [project / n for n in ['Conjecture236.lean', 'Check.lean',
    'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']]
inputs += [auxiliary / 'Inspect.lean', auxiliary / 'Audit.lean', Path(__file__)]
before = {str(x): sha(x) for x in inputs}
env = os.environ.copy()
env['PATH'] = str(binpath) + os.pathsep + env.get('PATH', '')
env.pop('LEAN_PATH', None)
env.pop('LEAN_SRC_PATH', None)
record = {'status': 'RUNNING', 'input_sha256': before, 'executions': []}
def save():
    (out / 'record.json').write_text(json.dumps(record, indent=2) + '\n')
save()
for name in ['Inspect.lean', 'Audit.lean']:
    shutil.copyfile(auxiliary / name, out / name)
    cmd = [str(binpath / 'lake'), 'env', 'lean', '-R', str(out),
        '-DwarningAsError=true', str(out / name)]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    r = subprocess.run(cmd, cwd=project, env=env, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, timeout=600)
    log = out / (name + '.txt')
    log.write_text(r.stdout)
    run = {'file': name, 'command': cmd, 'cwd': str(project),
        'started_utc': started, 'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'exit_code': r.returncode, 'output': log.name, 'output_sha256': sha(log)}
    record['executions'].append(run)
    save()
    assert r.returncode == 0, r.stdout
inspect = (out / 'Inspect.lean.txt').read_text()
audits = re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$", inspect, re.M)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
audit = (out / 'Audit.lean.txt').read_text()
checks = {
    'all_33_authored_axiom_audits': len(audits) == 33 and len({n for n, _ in audits}) == 33,
    'only_standard_axioms': all(set(x.strip() for x in values.split(',') if x.strip()) <= allowed for _, values in audits),
    'no_print_ellipses': '...' not in inspect and '⋯' not in inspect,
    'all_roots_in_safety_audit': 'Source roots: 33' in audit,
    'safe_logical_closure': 'No unsafe or partial declaration occurs in this transitive logical closure.' in audit,
    'no_unnecessary_runtime_artifacts': 'Generated runtime artifact' not in audit,
    'inputs_unchanged': before == {str(x): sha(x) for x in inputs},
    'inspection_sources_copied_exactly': all(sha(auxiliary / n) == sha(out / n) for n in ['Inspect.lean', 'Audit.lean']),
}
record.update(status='PASS' if all(checks.values()) else 'FAIL', checks=checks,
    scope='Read-only explicit declaration/definition/instance inspection and author safety-audit replay. Separate from complete module-origin audit and fresh proof build.')
save()
print(json.dumps({'status': record['status'], 'checks': checks}, indent=2))
assert all(checks.values()), 'Inspect complete evidence'
