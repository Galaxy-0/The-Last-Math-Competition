#!/usr/bin/env python3
"""Run an exact verification command and preserve its exit code and output."""
import datetime, json, pathlib, subprocess, sys
base = pathlib.Path('/private/tmp/tlmc525-author')
args = sys.argv[1:]
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
run = subprocess.run(args, cwd='/private/tmp/tlmc525-proof', text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
with (base / 'commands.jsonl').open('a') as out:
    out.write(json.dumps({'started_utc': started, 'cwd': '/private/tmp/tlmc525-proof', 'argv': args, 'exit_code': run.returncode, 'output': run.stdout}) + '\n')
sys.stdout.write(run.stdout)
print('RECORDED EXIT CODE:', run.returncode)
sys.exit(run.returncode)
