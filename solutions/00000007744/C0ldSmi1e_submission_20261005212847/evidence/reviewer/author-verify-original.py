from pathlib import Path
import subprocess, json, hashlib, re
root=Path('/private/tmp/tlmc7744-proof')
manifest=json.loads((root/'lake-manifest.json').read_text())
expected=json.loads(Path('/private/tmp/tlmc-pinned-dependencies.json').read_text())
assert manifest['packages']==expected['packages']
results=[]
for pkg in manifest['packages']:
 path=root/'.lake/packages'/pkg['name']
 rev=subprocess.run(['git','-C',str(path),'rev-parse','HEAD'],capture_output=True,text=True)
 status=subprocess.run(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],capture_output=True,text=True)
 assert rev.returncode==0 and status.returncode==0
 assert rev.stdout.strip()==pkg['rev'],pkg['name']
 assert not status.stdout.strip(),(pkg['name'],status.stdout)
 results.append({'name':pkg['name'],'expected':pkg['rev'],'actual':rev.stdout.strip(),'tracked_clean':True,'rev_exit':rev.returncode,'status_exit':status.returncode})
assert len(results)==9
inputs=[]
handoff=Path('/private/tmp/tlmc7744-eligibility/clean-math-handoff.json')
assert hashlib.sha256(handoff.read_bytes()).hexdigest()=='2169a848c256e17d1a6069cfefbb5296fe7c5ece91dff05ae7ce90a287bf7241'
data=json.loads(handoff.read_text())
for row in data['source_rules_metadata']:
 path=Path(row['path']); digest=hashlib.sha256(path.read_bytes()).hexdigest()
 assert digest==row['sha256']
 inputs.append({'path':str(path),'sha256':digest})
fingerprint=Path(data['input_fingerprint_path'])
assert hashlib.sha256(fingerprint.read_bytes()).hexdigest()==data['input_fingerprint_sha256']
files=[]
for path in sorted(root.iterdir()):
 if not path.is_file(): continue
 raw=path.read_bytes(); text=raw.decode()
 assert raw.endswith(b'\n') and not raw.endswith(b'\n\n'),path
 assert all(line==line.rstrip() for line in text.splitlines()),path
 files.append({'file':path.name,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
assert {r['file'] for r in files}=={'Conjecture7744.lean','Audit.lean','lakefile.toml','lake-manifest.json','lean-toolchain'}
source=(root/'Conjecture7744.lean').read_text()
assert not re.search(r'\b(sorry|admit|native_decide|unsafe|axiom)\b',source)
names=re.findall(r'^(?:def|theorem|instance)\s+([A-Za-z0-9_]+)',source,re.M)
audit=(root/'Audit.lean').read_text()
assert len(names)==49
assert audit.count('#print axioms')==len(names)
for name in names: assert '#print axioms Conjecture7744.'+name+'\n' in audit
output={'dependencies':results,'inputs':inputs,'proof_files':files,'named_declarations':names,'authored_count':len(names),'source_policy_scan':'PASS','whitespace':'PASS'}
Path('/private/tmp/tlmc7744-author/verification.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
