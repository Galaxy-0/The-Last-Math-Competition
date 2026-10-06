from pathlib import Path
import subprocess, os, json, hashlib, datetime, re

out = Path(__file__).resolve().parent
p = out / 'project'
env = os.environ.copy()
env['PATH'] = '/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin:' + env['PATH']
records = []
def hashes():
    return {f.name: hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.iterdir()) if f.is_file()}
def run(label, argv):
    dest = out / label
    dest.mkdir()
    rec = {'argv': argv, 'cwd': str(p), 'source_config_hashes_before': hashes(), 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    r = subprocess.run(argv, cwd=p, env=env, capture_output=True)
    rec.update({'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'exit_code': r.returncode, 'source_config_hashes_after': hashes()})
    (dest/'stdout.txt').write_bytes(r.stdout)
    (dest/'stderr.txt').write_bytes(r.stderr)
    (dest/'command.json').write_text(json.dumps(rec,indent=2)+'\n')
    records.append(rec)
    print(label, r.returncode, flush=True)
    assert r.returncode == 0, r.stdout.decode()+r.stderr.decode()
    assert rec['source_config_hashes_before'] == rec['source_config_hashes_after']
    return r.stdout.decode()

run('version', ['lean','--version'])
run('clean-full-build', ['lake','build'])
for module in ['Connectivity','IdealBridge','Conjecture545','Check','Audit']:
    run('strict-'+module, ['lake','env','lean','-DwarningAsError=true',module+'.lean'])
audit = run('full-inventory', ['lake','env','lean','-DwarningAsError=true','RootInventory.lean'])
entries=[]
allowed={'propext','Quot.sound','Classical.choice'}
for line in audit.splitlines():
    if not line.startswith('ROOT_DECL|'): continue
    _,module,name,kind,axioms=line.split('|')
    deps=[x.strip() for x in axioms.strip('[]').split(',') if x.strip()]
    entries.append({'module':module,'name':name,'kind':kind,'axioms':deps})
mathematical=[e for e in entries if e['module']!='Audit']
assert len(mathematical)==93
assert all(e['kind']!='axiom' and set(e['axioms'])<=allowed for e in mathematical)
assert {e['name'] for e in mathematical} == {line.split('\t')[1] for line in (p/'declaration-inventory.txt').read_text().splitlines() if '\t' in line}
(out/'compiled-declarations.json').write_text(json.dumps(entries,indent=2)+'\n')
pins=json.loads((p/'pinned-dependencies.json').read_text())
manifest=json.loads((p/'lake-manifest.json').read_text())
assert {x['name']:x['rev'] for x in pins['packages']} == {x['name']:x['rev'] for x in manifest['packages']}
for package in pins['packages']:
    path=p/'.lake/packages'/package['name']
    rev=run('pin-'+package['name'], ['git','-C',str(path),'rev-parse','HEAD']).strip()
    status=run('tracked-tree-'+package['name'], ['git','-C',str(path),'status','--porcelain','--untracked-files=no'])
    assert rev==package['rev'] and not status
for module in ['Connectivity','IdealBridge','Conjecture545','Check']:
    text=(p/(module+'.lean')).read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b', text)
result={'status':'ROOT_FROZEN_FULL_BUILD_STRICT_REPLAY_AND_MATHEMATICAL_AXIOM_AUDIT_PASS','mathematical_declaration_count':len(mathematical),'total_compiled_declarations_including_audit_tool':len(entries),'audit_tool_declarations':[e for e in entries if e['module']=='Audit'],'allowed_mathematical_axioms':sorted(allowed),'all_nine_pins_and_tracked_trees_match':True,'records':records,'publication_clearance':False}
(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
(out/'SHA256SUMS.json').write_text(json.dumps({str(f.relative_to(out)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(out.rglob('*')) if f.is_file() and '.lake' not in f.parts},indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='records'}),flush=True)
