#!/usr/bin/env python3
"""Record complete subprocess streams and recursive authored project snapshots."""
import datetime, hashlib, json, os, pathlib, shutil, subprocess, sys, time
root = pathlib.Path('/private/tmp/tlmc545-author')
project = pathlib.Path('/private/tmp/tlmc545-proof')
runs = root / 'runs'
runs.mkdir(parents=True, exist_ok=True)
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
dest = runs / stamp
dest.mkdir()
def snapshot(label):
    out = dest / label
    for base in [project, root]:
        for p in base.rglob('*'):
            rel = p.relative_to(base)
            if any(x in {'.lake', '.git', 'runs', '__pycache__'} for x in rel.parts):
                continue
            if p.is_file() and not p.is_symlink():
                q = out / base.name / rel
                q.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(p,q)
    hashes = {str(p.relative_to(out)):hashlib.sha256(p.read_bytes()).hexdigest()
              for p in out.rglob('*') if p.is_file()}
    (dest / (label + '-sha256.json')).write_text(json.dumps(hashes,indent=2)+'\n')
cmd = sys.argv[1:]
env = dict(os.environ)
env['PATH'] = '/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin:' + env.get('PATH','')
meta = {'argv':cmd,'cwd':str(project),'started_utc':stamp,'path':env['PATH']}
(dest/'command.json').write_text(json.dumps(meta,indent=2)+'\n')
snapshot('before')
start = time.monotonic()
proc = subprocess.run(cmd,cwd=project,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
(dest/'stdout.txt').write_bytes(proc.stdout)
(dest/'stderr.txt').write_bytes(proc.stderr)
meta.update(exit_code=proc.returncode,elapsed_seconds=time.monotonic()-start)
(dest/'result.json').write_text(json.dumps(meta,indent=2)+'\n')
snapshot('after')
sys.stdout.buffer.write(proc.stdout)
sys.stderr.buffer.write(proc.stderr)
print('\nRECORD:',dest,'EXIT:',proc.returncode,flush=True)
sys.exit(proc.returncode)
