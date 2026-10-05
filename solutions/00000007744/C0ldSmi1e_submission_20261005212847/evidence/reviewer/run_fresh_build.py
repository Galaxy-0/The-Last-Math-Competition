from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys

review = Path('/private/tmp/tlmc7744-review')
project = review / 'fresh-proof'
runtime = '/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin'
environment = dict(os.environ)
environment['PATH'] = runtime + ':' + environment['PATH']
commands = [
    ('lean-version', [runtime + '/lean', '--version']),
    ('lake-build', [runtime + '/lake', 'build']),
    *[(module + '-strict', [runtime + '/lake', 'env', 'lean', '-DwarningAsError=true',
                          '-o', str(project / '.lake/build/lib/lean' / (module + '.olean')),
                          module + '.lean'])
      for module in ['Conjecture7744', 'Audit', 'Check']],
]
for label, command in commands:
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result = subprocess.run(command, cwd=project, env=environment, capture_output=True)
    (review / (label + '.stdout.txt')).write_bytes(result.stdout)
    (review / (label + '.stderr.txt')).write_bytes(result.stderr)
    record = {'label': label, 'command': command, 'cwd': str(project),
              'started_utc': started, 'exit_code': result.returncode,
              'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'stdout_sha256': hashlib.sha256(result.stdout).hexdigest(),
              'stderr_sha256': hashlib.sha256(result.stderr).hexdigest()}
    with (review / 'fresh-build-execution.jsonl').open('a') as log:
        log.write(json.dumps(record) + '\n')
    print(json.dumps(record), flush=True)
    if result.returncode:
        sys.exit(result.returncode)
