import sys, subprocess, os, json, datetime
from pathlib import Path
root=Path('/private/tmp/tlmc7744-author')
args=sys.argv[1:]
stamp=datetime.datetime.now().strftime('%Y%m%dT%H%M%S%f')
env=os.environ.copy(); env['PATH']='/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin:'+env['PATH']
snapshot=root/('source-'+stamp)
snapshot.mkdir()
for src in Path('/private/tmp/tlmc7744-proof').iterdir():
 if src.is_file(): (snapshot/src.name).write_bytes(src.read_bytes())
r=subprocess.run(args,cwd='/private/tmp/tlmc7744-proof',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(root/(stamp+'.log')).write_text(r.stdout)
with (root/'commands.jsonl').open('a') as f: f.write(json.dumps({'time':stamp,'cwd':'/private/tmp/tlmc7744-proof','args':args,'exit_code':r.returncode,'log':stamp+'.log'})+'\n')
print(r.stdout,end=''); print('ACTUAL_EXIT_CODE='+str(r.returncode)); sys.exit(r.returncode)
