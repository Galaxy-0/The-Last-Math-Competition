#!/usr/bin/env python3
"""Preserve document command streams, statuses, and exact source snapshots."""
import datetime, hashlib, json, pathlib, shutil, subprocess, sys, time
root=pathlib.Path('/private/tmp/tlmc545-document')
identity=json.loads(pathlib.Path('/private/tmp/tlmc545-package-location.json').read_text())
package=pathlib.Path(identity['folder'])
runs=root/'runs'
runs.mkdir(exist_ok=True)
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
out=runs/stamp
out.mkdir()
def snapshot(label):
    d=out/label
    d.mkdir()
    authored=[p for p in root.rglob('*') if p.is_file()
              and not any(x in {'runs','export','render','__pycache__'} for x in p.relative_to(root).parts)]
    for source in authored+[package/'report.tex',package/'report.pdf']:
        if source.exists():
            target=d/('package' if source.parent==package else 'author')/source.name
            target.parent.mkdir(exist_ok=True)
            shutil.copy2(source,target)
    hashes={str(p.relative_to(d)):hashlib.sha256(p.read_bytes()).hexdigest() for p in d.rglob('*') if p.is_file()}
    (out/(label+'-sha256.json')).write_text(json.dumps(hashes,indent=2)+'\n')
argv=sys.argv[1:]
meta={'argv':argv,'cwd':str(root),'package_identity':identity,'started_utc':stamp}
(out/'command.json').write_text(json.dumps(meta,indent=2)+'\n')
snapshot('before')
start=time.monotonic()
r=subprocess.run(argv,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
(out/'stdout.txt').write_bytes(r.stdout)
(out/'stderr.txt').write_bytes(r.stderr)
meta.update(exit_code=r.returncode,elapsed_seconds=time.monotonic()-start)
(out/'result.json').write_text(json.dumps(meta,indent=2)+'\n')
snapshot('after')
sys.stdout.buffer.write(r.stdout)
sys.stderr.buffer.write(r.stderr)
print('\nDOCUMENT RECORD:',out,'EXIT:',r.returncode)
sys.exit(r.returncode)
