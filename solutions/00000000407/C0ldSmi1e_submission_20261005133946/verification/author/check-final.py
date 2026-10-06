import pathlib,json,hashlib,re,subprocess
p=pathlib.Path('/private/tmp/tlmc407-proof')
a=pathlib.Path('/private/tmp/tlmc407-author')
m=json.loads((p/'lake-manifest.json').read_text())
s=json.loads(pathlib.Path('/private/tmp/tlmc407-author-input/pinned-dependencies.json').read_text()); s['name']='tlmc407'
assert m==s
checks=[]
for pkg in m['packages']:
    d=p/'.lake/packages'/pkg['name']
    r=subprocess.run(['git','-C',str(d),'rev-parse','HEAD'],text=True,capture_output=True)
    row={'name':pkg['name'],'expected':pkg['rev'],'actual':r.stdout.strip(),'exit_code':r.returncode}
    assert row['actual']==row['expected'], row
    checks.append(row)
files=['Conjecture407.lean','Audit407.lean','lakefile.toml','lean-toolchain','lake-manifest.json']
hashes={f:hashlib.sha256((p/f).read_bytes()).hexdigest() for f in files}
for f in ['Conjecture407.lean','Audit407.lean']:
    hits=re.findall(r'\b(?:sorry|admit|native_decide|axiom|unsafe|partial|meta)\b',(p/f).read_text())
    assert not hits,(f,hits)
rows=[json.loads(l) for l in (a/'commands.jsonl').read_text().splitlines()]
last_axioms=next(r for r in reversed(rows) if r['command'][-1]=='/private/tmp/tlmc407-author/AllAxioms.lean')
assert last_axioms['exit_code']==0
allowed={'propext','Classical.choice','Quot.sound'}
for axiom_list in re.findall(r'depends on axioms: \[([^]]*)\]',last_axioms['output'],re.S):
    found={x.strip() for x in axiom_list.split(',')}
    assert found<=allowed, found
(a/'all-axioms-final.txt').write_text(last_axioms['output'])
(a/'checks-final.json').write_text(json.dumps({'manifest_exact':True,'dependency_heads':checks,'source_hashes':hashes,'forbidden_token_hits':[],'all_declaration_axioms_within':sorted(allowed),'declaration_count':len((a/'declarations.txt').read_text().splitlines())},indent=2)+'\n')
print((a/'checks-final.json').read_text())
