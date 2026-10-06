from pathlib import Path
import json, re, hashlib, datetime
p=Path(__file__).resolve().parent
text=(p/'full-inventory/stdout.txt').read_text()
entries=[]
for match in re.finditer(r'^ROOT_DECL\|([^|\n]+)\|([^|\n]+)\|([^|\n]+)\|(\[[\s\S]*?\])',text,re.M):
    module,name,kind,raw=match.groups()
    entries.append({'module':module,'name':name,'kind':kind,'axioms':[a.strip() for a in raw.strip('[]').split(',') if a.strip()]})
assert len(entries)==text.count('ROOT_DECL|')==93
expected={}
for line in (p/'project/declaration-inventory.txt').read_text().splitlines():
    if '\t' not in line: continue
    module,name,raw=line.split('\t')
    expected[name]=(module,{a.strip() for a in raw.strip('[]').split(',') if a.strip()})
assert len(expected)==93
assert all((e['module'],set(e['axioms']))==expected[e['name']] for e in entries)
assert all(e['kind']!='axiom' and set(e['axioms'])<={'propext','Quot.sound','Classical.choice'} for e in entries)
(p/'compiled-declarations.json').write_text(json.dumps(entries,indent=2)+'\n')
rec={'status':'PASS','verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'compiled_declaration_count':93,'all_names_modules_and_complete_axiom_sets_match':True,'purpose':'Parse multiline Lean diagnostic lists in full; the initial line-based parser shortened one axiom list. Actual compilation/audit output is unchanged and the complete list contains only the three standard axioms.','audit_stdout_sha256':hashlib.sha256(text.encode()).hexdigest()}
(p/'inventory-parse-validation.json').write_text(json.dumps(rec,indent=2)+'\n')
r=json.loads((p/'result.json').read_text());r['complete_multiline_inventory_validation']=rec;(p/'result.json').write_text(json.dumps(r,indent=2)+'\n')
(p/'SHA256SUMS.json').write_text(json.dumps({str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*')) if f.is_file() and '.lake' not in f.parts and f.name!='SHA256SUMS.json'},indent=2)+'\n')
print(json.dumps(rec))
