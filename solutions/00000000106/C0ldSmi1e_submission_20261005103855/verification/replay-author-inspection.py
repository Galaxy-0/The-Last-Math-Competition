"""Replay the author's read-only Lean inspection against a specified built project."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--project', required=True, type=Path)
parser.add_argument('--inspection', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
parser.add_argument('--lean-bin', required=True, type=Path)
args = parser.parse_args()
project, source, out, binpath = [p.resolve() for p in
    (args.project, args.inspection, args.output, args.lean_bin)]
assert not out.exists(), 'Use a new output directory'
out.mkdir()
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
proof = project / 'Conjecture106.lean'
before = {'proof': sha(proof), 'inspection': sha(source), 'script': sha(Path(__file__))}
shutil.copyfile(source, out / 'Inspect.lean')
env = os.environ.copy()
env['PATH'] = str(binpath) + os.pathsep + env.get('PATH', '')
env.pop('LEAN_PATH', None)
env.pop('LEAN_SRC_PATH', None)
cmd = [str(binpath / 'lake'), 'env', 'lean', '-R', str(out),
       '-DwarningAsError=true', str(out / 'Inspect.lean')]
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
r = subprocess.run(cmd, cwd=project, env=env, capture_output=True, text=True, timeout=600)
raw = r.stdout + r.stderr
(out / 'inspection.txt').write_text(raw)
entries = re.findall(r'^AXIOMS (\S+) : \[(.*?)\]', raw, re.M | re.S)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
audits = [{'name': n, 'axioms': [s.strip() for s in a.split(',') if s.strip()]}
          for n, a in entries]
checks = {
    'strict_replay_succeeded': r.returncode == 0,
    'all_26_compiled_namespace_declarations_reported': len(entries) == 26,
    'distinct_declaration_names': len({n for n, _ in entries}) == len(entries),
    'only_standard_axioms': all(set(a['axioms']) <= allowed for a in audits),
    'all_three_authored_definitions_safe': raw.count('Lean.DefinitionSafety.safe') == 3,
    'no_unsafe_authored_definition': 'Lean.DefinitionSafety.unsafe' not in raw,
    'inspection_copied_exactly': sha(out / 'Inspect.lean') == before['inspection'],
    'inputs_unchanged': before == {'proof': sha(proof), 'inspection': sha(source),
                                 'script': sha(Path(__file__))},
}
record = {'status': 'PASS' if all(checks.values()) else 'FAIL',
          'started_utc': started,
          'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'command': cmd, 'cwd': str(project), 'exit_code': r.returncode,
          'checks': checks, 'input_sha256': before, 'audits': audits,
          'output_sha256': sha(out / 'inspection.txt'),
          'scope': 'Read-only author inspection replay; proof has already been built separately. '
                   'This does not replace the exhaustive module-origin and dependency-closure audit.'}
(out / 'record.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'status': record['status'], 'checks': checks}, indent=2))
assert all(checks.values()), 'Inspect record.json and inspection.txt'
