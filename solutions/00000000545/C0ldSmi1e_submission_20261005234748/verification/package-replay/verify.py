#!/usr/bin/env python3
"""Rebuild and audit the complete conjecture 545 proof; Python standard library only."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import tempfile

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='New directory for complete execution records')
    parser.add_argument('--lake', default='lake', help='Lake executable for Lean 4.19.0')
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    project = base / 'lean'
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='conjecture545-verification-'))
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
    records = []
    modules = ['Connectivity', 'IdealBridge', 'Conjecture545', 'Check', 'Audit']
    expected = json.loads((base/'verification/author/author-freeze.json').read_text())
    inputs = [project/(m+'.lean') for m in modules] + [project/n for n in ['lean-toolchain','lakefile.toml','lake-manifest.json','pinned-dependencies.json']]
    before = {str(p.relative_to(base)): sha(p) for p in inputs}
    for p in inputs:
        if sha(p) != expected['source_sha256'][p.name]:
            raise RuntimeError('Frozen source/configuration mismatch: '+str(p))
    if sha(base/'ORIGINAL.md') != expected['original_source_sha256']:
        raise RuntimeError('Original conjecture identity mismatch')
    for p in inputs:
        if p.suffix == '.lean' and re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b',p.read_text()):
            raise RuntimeError('Prohibited proof construct: '+str(p))
    if sorted(p.name for p in project.glob('*.lean')) != sorted(m+'.lean' for m in modules):
        raise RuntimeError('Unexpected or missing authored Lean module')

    def run(label, argv):
        dest = out/label
        dest.mkdir()
        rec = {'argv':argv,'cwd':str(project),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_sha256':before}
        result = subprocess.run(argv,cwd=project,capture_output=True)
        rec.update({'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':result.returncode})
        (dest/'stdout.txt').write_bytes(result.stdout)
        (dest/'stderr.txt').write_bytes(result.stderr)
        (dest/'command.json').write_text(json.dumps(rec,indent=2)+'\n')
        records.append(rec)
        print(label, 'PASS' if result.returncode==0 else 'FAIL',flush=True)
        if result.returncode:
            raise RuntimeError(result.stdout.decode(errors='replace')+result.stderr.decode(errors='replace'))
        return result.stdout.decode()

    pins=json.loads((project/'pinned-dependencies.json').read_text())['packages']
    manifest=json.loads((project/'lake-manifest.json').read_text())['packages']
    if {p['name']:p['rev'] for p in pins}!={p['name']:p['rev'] for p in manifest}:
        raise RuntimeError('Dependency manifests disagree')
    def check_pins(stage):
        for package in pins:
            path=project/'.lake/packages'/package['name']
            rev=run(stage+'-revision-'+package['name'],['git','-C',str(path),'rev-parse','HEAD']).strip()
            dirty=run(stage+'-tracked-tree-'+package['name'],['git','-C',str(path),'status','--porcelain','--untracked-files=no'])
            if rev!=package['rev'] or dirty:
                raise RuntimeError('Wrong or modified dependency: '+package['name'])

    version=run('lean-version',[args.lake,'env','lean','--version'])
    if 'version 4.19.0,' not in version:
        raise RuntimeError('Expected Lean 4.19.0')
    check_pins('before')
    run('full-build',[args.lake,'build'])
    audit=''
    for module in modules:
        text=run('strict-'+module,[args.lake,'env','lean','-DwarningAsError=true',module+'.lean'])
        if module=='Audit':
            audit=text
    entries=[]
    for match in re.finditer(r'^DECL (\S+) (\S+) AXIOMS (\[[\s\S]*?\])',audit,re.M):
        module,name,raw=match.groups()
        axioms={a.strip() for a in raw.strip('[]').split(',') if a.strip()}
        if not axioms<={'propext','Quot.sound','Classical.choice'}:
            raise RuntimeError('Unexpected axiom dependencies: '+name)
        entries.append({'module':module,'name':name,'axioms':sorted(axioms)})
    inventory={}
    for line in (base/'verification/author/declaration-inventory.txt').read_text().splitlines():
        if '\t' not in line:
            continue
        module,name,raw=line.split('\t')
        inventory[name]=(module,{a.strip() for a in raw.strip('[]').split(',') if a.strip()})
    totals=re.findall(r'AUTHORED_DECLARATION_TOTAL (\d+)',audit)
    if totals!=['93'] or len(entries)!=len(inventory)!=93:
        raise RuntimeError('Declaration inventory size mismatch')
    if len(entries)!=93 or {e['name'] for e in entries}!=set(inventory):
        raise RuntimeError('Compiled declaration inventory differs')
    if any((e['module'],set(e['axioms']))!=inventory[e['name']] for e in entries):
        raise RuntimeError('Complete compiled axiom inventory differs')
    check_pins('after')
    after={str(p.relative_to(base)):sha(p) for p in inputs}
    if before!=after:
        raise RuntimeError('Input files changed during verification')
    summary={'status':'PASS','candidate':'00000000545','final_theorem':'CompleteGraph.conjecture545_false_positive','full_build':True,'warnings_as_errors_modules':modules,'compiled_declarations':entries,'all_nine_pinned_revisions_and_tracked_trees_unchanged':True,'input_sha256':after,'auxiliary_mathematical_computations':'None; unrestricted symbolic proof.','maintainer_acceptance':'Not asserted by this local verification.','records':records}
    (out/'result.json').write_text(json.dumps(summary,indent=2)+'\n')
    (out/'verify.py').write_bytes(Path(__file__).read_bytes())
    (out/'SHA256SUMS.json').write_text(json.dumps({str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file()},indent=2)+'\n')
    print('PASS: full build, strict replay, 93 declarations, standard axioms, nine pinned dependencies.')
    print('Execution records: '+str(out))

if __name__=='__main__':
    main()
