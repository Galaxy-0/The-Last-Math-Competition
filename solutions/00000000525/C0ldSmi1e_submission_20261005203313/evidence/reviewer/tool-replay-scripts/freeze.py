#!/usr/bin/env python3
"""Freeze exact validated source and configuration bytes; no mathematical computation."""
import datetime, hashlib, json, pathlib, re, tomllib
base = pathlib.Path('/private/tmp/tlmc525-review/tool-replay-project')
author = pathlib.Path('/private/tmp/tlmc525-review/tool-replay-evidence')
paths = ['Conjecture525.lean', 'Audit.lean', 'lakefile.toml', 'lean-toolchain', 'lake-manifest.json']
assert sorted(p.name for p in base.iterdir() if p.is_file()) == sorted(paths)
config = tomllib.loads((base/'lakefile.toml').read_text())
assert config['name'] == 'conjecture525'
assert config['defaultTargets'] == ['Conjecture525', 'Audit']
assert config['leanOptions']['autoImplicit'] is False
assert config['require'][0]['rev'] == 'v4.19.0'
for name in ['Conjecture525.lean','Audit.lean']:
    content = (base/name).read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|(?m:^\s*(axiom|unsafe|opaque)\b)', content)
records = [json.loads(line) for line in (author/'commands.jsonl').read_text().splitlines()]
for suffix in [['lake','build'], ['lake','env','lean','-DwarningAsError=true','Conjecture525.lean'], ['lake','env','lean','-DwarningAsError=true','Audit.lean']]:
    matching = [r for r in records if [pathlib.Path(r['argv'][0]).name]+r['argv'][1:] == suffix]
    assert matching and matching[-1]['exit_code'] == 0
    assert 'warning:' not in matching[-1]['output']
    if suffix[-1] == 'Audit.lean':
        assert 'Audited 63 authored declarations' in matching[-1]['output']
deps=json.loads((author/'dependency-verification.json').read_text())
assert len(deps) == 9 and all(r['pin_matches'] and r['tracked_clean'] for r in deps)
manifest = {'status':'frozen-ready', 'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(), 'proof_directory':str(base), 'lean_version':'4.19.0', 'authored_declaration_count':63, 'allowed_axioms':['propext','Classical.choice','Quot.sound'], 'files':[{'path':name,'sha256':hashlib.sha256((base/name).read_bytes()).hexdigest(),'bytes':(base/name).stat().st_size} for name in paths], 'semantics_sha256':hashlib.sha256((author/'semantics.txt').read_bytes()).hexdigest(), 'commands':str(author/'commands.jsonl'), 'dependency_verification':str(author/'dependency-verification.json'), 'provenance':str(author/'provenance.txt')}
(author/'FROZEN.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))
