"""Independent frozen-input execution verifier for conjecture 637.

This is auxiliary inspection tooling, not part of the submitted mathematical
proof. It never runs against the candidate until --ready is explicitly supplied.
The environment harness inventories every compiled declaration whose *module of
origin* is one of the submitted implementation modules, including generated
structure/instance machinery. Its use of Lean metaprogramming is confined to
printing types, collecting axioms and traversing existing dependencies; it proves no submitted theorem.
"""
import argparse, datetime, hashlib, json, os, pathlib, re, shutil, subprocess, sys, time
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--ready',action='store_true')
parser.add_argument('--source',type=pathlib.Path,default=pathlib.Path('/private/tmp/tlmc637-proof'))
parser.add_argument('--build-dir',type=pathlib.Path,default=pathlib.Path('/private/tmp/tlmc637-independent-final'))
parser.add_argument('--evidence-dir',type=pathlib.Path,default=pathlib.Path('/private/tmp/tlmc637-verification'))
parser.add_argument('--lean-bin',type=pathlib.Path,default=pathlib.Path('/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin'))
parser.add_argument('--packages',type=pathlib.Path,default=pathlib.Path('/private/tmp/tlmc637-proof/.lake/packages'))
parser.add_argument('--audit-names',type=pathlib.Path,default=pathlib.Path('/private/tmp/tlmc637-audit-names.json'))
parser.add_argument('--frozen-sources',type=pathlib.Path,default=pathlib.Path('/private/tmp/tlmc637-frozen-sources.json'))
args=parser.parse_args()
assert args.ready, 'Run only after the explicit freeze/ready notification, with --ready'
src=args.source.resolve()
dst=args.build_dir.resolve()
out=args.evidence_dir.resolve()
binpath=args.lean_bin.resolve()
pkgs=args.packages.resolve()
inventory_path=args.audit_names.resolve()
frozen_identity_path=args.frozen_sources.resolve()
frozen_identity=json.loads(frozen_identity_path.read_text())
frozen_identity_sha256=hashlib.sha256(frozen_identity_path.read_bytes()).hexdigest()
audit_names=json.loads(inventory_path.read_text())
expected_def_count=len(audit_names['definitions'])
expected_audit_count=len(audit_names['theorems'])
expected_instance_count=len(audit_names['instances'])
# Every named instance found by the independent declaration scan must have
# a matching inventory entry plus emitted type and transitive-axiom audit.
instance_names=set(audit_names['instances'])
# The exact instance list is dynamic and must equal the independent source scan.
assert set(audit_names['instances'])<=set(audit_names['theorems'])
expected_theorem_count=sum(d['kind'] in {'theorem','lemma'} for d in audit_names['declarations'])
assert expected_audit_count==expected_theorem_count+expected_instance_count
assert expected_def_count>=0 and expected_theorem_count>0
assert len(audit_names['declarations'])==expected_def_count+expected_theorem_count+expected_instance_count
assert len(set(audit_names['definitions']))==expected_def_count
assert len(set(audit_names['theorems']))==expected_audit_count
assert len(set(audit_names['instances']))==expected_instance_count
all_sources=sorted(str(p.relative_to(src)) for p in src.rglob('*.lean') if '.lake' not in p.relative_to(src).parts)
assert 'Conjecture637.lean' in all_sources and 'Check.lean' in all_sources
assert all(not (src/n).is_symlink() for n in all_sources)
module_to_file={n[:-5].replace('/','.'):n for n in all_sources}
local_imports={n:[] for n in all_sources}
for n in all_sources:
 for line in (src/n).read_text().splitlines():
  if line.startswith('import '):
   for module in line[7:].split('--')[0].split():
    if module in module_to_file:local_imports[n].append(module_to_file[module])
sources=[]; visiting=set(); visited=set()
def visit(name):
 assert name not in visiting, 'Local import cycle: '+name
 if name in visited:return
 visiting.add(name)
 for dependency in local_imports[name]:visit(dependency)
 visiting.remove(name);visited.add(name);sources.append(name)
visit('Conjecture637.lean');visit('Check.lean')
assert visited==set(all_sources), 'Some source modules are not imported by the root or Check; explicitly review build coverage'
assert sources[-1]=='Check.lean'
configs=['lakefile.toml','lake-manifest.json','lean-toolchain']
assert len(configs)==3
# Final module count and paths come from the complete frozen source tree.
# The import traversal above must cover every discovered Lean file.
assert set(frozen_identity)==set(sources+configs), 'Frozen file manifest must cover every source and all three configs exactly'
assert frozen_identity=={n:hashlib.sha256((src/n).read_bytes()).hexdigest() for n in sources+configs}, 'Source differs from the explicit frozen identity record'
assert not dst.exists(), 'Fresh directory must not exist'
dst.mkdir(); (dst/'.lake').mkdir(); (dst/'.lake/packages').symlink_to(pkgs, target_is_directory=True)
for name in sources+configs:
 p=dst/name; p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src/name,p)
assert not (dst/'.lake/build').exists()
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
report={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_root':str(src),'independent_root':str(dst),'dependency_root':str(pkgs),'fresh_build_outputs_absent':True,'copied_files':sources+configs,'source_sha256':{n:sha(src/n) for n in sources+configs},'dependencies':[],'strict_replay':[],'verifier_sha256':sha(pathlib.Path(__file__)),'audit_inventory_sha256_before':sha(inventory_path),'expected_counts':{'definitions_abbreviations_structures':expected_def_count,'theorems':expected_theorem_count,'named_instances':expected_instance_count,'type_and_axiom_audits':expected_audit_count},'local_imports':local_imports,'named_instance_names':sorted(instance_names)}
report['frozen_identity_record']={'path':str(frozen_identity_path),'sha256':frozen_identity_sha256,'source_hashes_match_before':report['source_sha256']==frozen_identity}
out.mkdir(exist_ok=True)
def save(): (out/'strict-replay.json').write_text(json.dumps(report,indent=2)+'\n')
command_records=[]
command_dir=out/'commands'
command_dir.mkdir(exist_ok=True)
def run(args,cwd=dst,timeout=600):
 import signal
 env=os.environ.copy();env['PATH']=str(binpath)+os.pathsep+env.get('PATH','');env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
 number=len(command_records)+1;log=command_dir/f'{number:04d}.log'
 entry={'index':number,'argv':list(map(str,args)),'cwd':str(cwd),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'timeout_seconds':timeout,'combined_output':str(log),'status':'RUNNING'}
 command_records.append(entry)
 (out/'execution-records.json').write_text(json.dumps(command_records,indent=2)+'\n')
 with log.open('wb') as stream:
  proc=subprocess.Popen(args,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
  try:
   code=proc.wait(timeout=timeout)
  except subprocess.TimeoutExpired:
   entry['timed_out']=True
   os.killpg(proc.pid,signal.SIGTERM)
   try:proc.wait(timeout=10)
   except subprocess.TimeoutExpired:
    os.killpg(proc.pid,signal.SIGKILL);proc.wait()
   code=124
 content=log.read_text()
 entry.update(completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit_code=code,status='PASS' if code==0 else 'FAIL',output_sha256=sha(log))
 (out/'execution-records.json').write_text(json.dumps(command_records,indent=2)+'\n')
 return subprocess.CompletedProcess(args,code,stdout=content)

manifest=json.loads((dst/'lake-manifest.json').read_text())
assert len(manifest['packages'])==9
expected_dependency_pins={
 'mathlib':'c44e0c8ee63ca166450922a373c7409c5d26b00b',
 'plausible':'77e08eddc486491d7b9e470926b3dbe50319451a',
 'LeanSearchClient':'25078369972d295301f5a1e53c3e5850cf6d9d4c',
 'importGraph':'e6a9f0f5ee3ccf7443a0070f92b62f8db12ae82b',
 'proofwidgets':'c4919189477c3221e6a204008998b0d724f49904',
 'aesop':'5d50b08dedd7d69b3d9b3176e0d58a23af228884',
 'Qq':'fa4f7f15d97591a9cf3aa7724ba371c7fc6dda02',
 'batteries':'f5d04a9c4973d401c8c92500711518f7c656f034',
 'Cli':'02dbd02bc00ec4916e99b04b2245b30200e200d0',
}
assert {p['name']:p['rev'] for p in manifest['packages']}==expected_dependency_pins
report['expected_dependency_pins']=expected_dependency_pins
for p in manifest['packages']:
 root=pkgs/p['name'];head=run(['git','rev-parse','HEAD'],root);status=run(['git','status','--porcelain','--untracked-files=no'],root)
 d={'name':p['name'],'expected_rev':p['rev'],'actual_rev':head.stdout.strip(),'head_command':['git','rev-parse','HEAD'],'head_exit_code':head.returncode,'status_command':['git','status','--porcelain','--untracked-files=no'],'status_exit_code':status.returncode,'revision_matches':head.returncode==0 and head.stdout.strip()==p['rev'],'tracked_status':status.stdout,'tracked_clean':status.returncode==0 and status.stdout==''};report['dependencies'].append(d);save()
 assert d['revision_matches'] and d['tracked_clean'],d
version=run([str(binpath/'lean'),'--version']);report['lean_version']={'exit_code':version.returncode,'output':version.stdout.strip()};save()
assert version.returncode==0 and 'version 4.19.0,' in version.stdout
githash=run([str(binpath/'lean'),'--githash'])
report['lean_commit']={'exit_code':githash.returncode,'expected':'6caaee842e9495688c1567e78c0e68dbb96942aa','actual':githash.stdout.strip()}
assert githash.returncode==0 and githash.stdout.strip()==report['lean_commit']['expected']
import tomllib
config=tomllib.loads((dst/'lakefile.toml').read_text())
report['project_identity']={'manifest_name':manifest['name'],'lake_name':config['name'],'default_targets':config['defaultTargets'],'toolchain_pin':(dst/'lean-toolchain').read_text().strip(),'source_file_count':len(sources),'config_file_count':len(configs),'dependency_symlink_target':str((dst/'.lake/packages').resolve())}
assert manifest['name']==config['name']=='conjecture637'
assert config['defaultTargets']==['Conjecture637','Audit']
assert report['project_identity']['toolchain_pin']=='leanprover/lean4:v4.19.0'
assert report['project_identity']['dependency_symlink_target']==str(pkgs.resolve())
pattern=re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafe|partial|run_tac|run_elab|elab|macro|initialize|builtin_initialize|implemented_by|extern|skipKernelTC)\b|Lean\.ofReduceBool|debug\.skipKernelTC|trustLevel|#eval\b')
def mask_lean_comments_strings(source):
 out=list(source);i=0;depth=0;line_comment=False;string=False
 while i<len(source):
  if line_comment:
   if source[i]=='\n':line_comment=False
   else:out[i]=' '
   i+=1;continue
  if depth:
   if source.startswith('/-',i):out[i]=out[i+1]=' ';depth+=1;i+=2;continue
   if source.startswith('-/',i):out[i]=out[i+1]=' ';depth-=1;i+=2;continue
   if source[i]!='\n':out[i]=' '
   i+=1;continue
  if string:
   if source[i]=='\\' and i+1<len(source):out[i]=out[i+1]=' ';i+=2;continue
   if source[i]=='"':string=False
   if source[i]!='\n':out[i]=' '
   i+=1;continue
  if source.startswith('--',i):out[i]=out[i+1]=' ';line_comment=True;i+=2;continue
  if source.startswith('/-',i):out[i]=out[i+1]=' ';depth=1;i+=2;continue
  if source[i]=='"':out[i]=' ';string=True
  i+=1
 assert not depth and not string,'Unclosed comment or string in source scanner'
 return ''.join(out)
# Lean permits keywords as guillemet-quoted identifier components. Normalize
# simple quoted spellings, including «prefix», to their logical qualified names.
# More complex quoted names fail the coverage check instead of being truncated.
lean_name_pattern=r"(?:«[\w\x27]+»|[\w][\w\x27]*)(?:\.(?:«[\w\x27]+»|[\w][\w\x27]*))*"
def normalize_lean_name(name):
 assert re.fullmatch(lean_name_pattern,name), 'Explicit audit mapping required for identifier: '+name
 return re.sub(r'«([\w\x27]+)»',r'\1',name)
# Independent source inventory cross-check. Fail closed on anonymous declarations
# rather than assuming a compiler-generated name or silently excluding a proof.
source_declarations=[]; unnamed=[]; unsupported=[]
declaration_re=re.compile(r"^(?:@\[[^\]]+\]\s+)*(?:(?:noncomputable|private|protected|partial|nonrec)\s+)*(def|abbrev|opaque|structure|class|inductive|theorem|lemma|instance|example)\b(.*)$")
for filename in sources:
 stack=[]
 for line_no,line in enumerate(mask_lean_comments_strings((dst/filename).read_text()).splitlines(),1):
  text=line.strip()
  ns=re.fullmatch(r'namespace\s+('+lean_name_pattern+r')',text)
  sec=re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+'+lean_name_pattern+r')?',text)
  end=re.fullmatch(r'end(?:\s+'+lean_name_pattern+r')?',text)
  if ns:stack.append(('namespace',normalize_lean_name(ns.group(1))));continue
  if sec:stack.append(('section',''));continue
  if end:
   assert stack, (filename,line_no,'Unmatched end in inventory scanner')
   stack.pop();continue
  match=declaration_re.match(text)
  if not match:continue
  assert filename!='Check.lean', 'Check.lean must contain inspection commands only, no unaudited declarations'
  kind,tail=match.groups();tail=tail.strip()
  if kind=='instance':tail=re.sub(r'^\(priority\s*:=.*?\)\s*','',tail)
  named=re.match('('+lean_name_pattern+r')(?=\s|:|\(|\{|\[|$)',tail)
  if kind=='example' or not named:
   unnamed.append({'file':filename,'line':line_no,'kind':kind,'declaration':text});continue
  if re.search(r'\bprivate\b',text[:match.start(1)]):
   unsupported.append({'file':filename,'line':line_no,'kind':kind,'reason':'Private declarations need explicit compiled-name mapping'});continue
  name=normalize_lean_name(named.group(1))
  prefix='.'.join(value for tag,value in stack if tag=='namespace')
  qualified=name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(x for x in [prefix,name] if x)
  source_declarations.append({'kind':kind,'name':qualified,'file':filename,'line':line_no})
 assert all(tag=='section' for tag,value in stack),(filename,'Unclosed namespace in inventory scanner')
 # Lean permits a section, including noncomputable section, to extend to end of file.
report['source_declaration_inventory']={'declarations':source_declarations,'unnamed_declarations':unnamed,'unsupported_declarations':unsupported,'method':'Line-based independent declaration scan after masking comments/strings, tracking namespaces and sections. Simple guillemet-quoted components such as «prefix» normalize to logical names. Anonymous/private or unsupported quoted declarations require explicit review rather than silent omission.'}
save()
assert not unnamed and not unsupported, 'Explicit audit coverage required for unnamed/private declarations; see source_declaration_inventory'
def canonical_declaration(d):
 return (d['file'],d['line'],{'lemma':'theorem','class':'structure'}.get(d['kind'],d['kind']),d['name'])
assert sorted(map(canonical_declaration,source_declarations))==sorted(map(canonical_declaration,audit_names['declarations'])), 'Audit inventory does not cover the actual source declarations exactly'
report['source_declaration_inventory']['matches_supplied_inventory']=True
source_instance_names=[d['name'] for d in source_declarations if d['kind']=='instance']
assert set(source_instance_names)==set(audit_names['instances']), 'Named instances must match the independently scanned source inventory'
assert len(source_instance_names)==len(set(source_instance_names)), 'Duplicate named instance in independent source inventory'
report['named_instance_coverage']={'qualified_names':sorted(instance_names),'present_as_source_instances':True,'present_in_supplied_instance_inventory':True}
save()
raw_hits=[];code_hits=[]
for n in sources:
 source=(dst/n).read_text();masked=mask_lean_comments_strings(source)
 for i,(raw,code) in enumerate(zip(source.splitlines(),masked.splitlines()),1):
  if pattern.search(raw):raw_hits.append({'file':n,'line':i,'text':raw,'code_hit':bool(pattern.search(code))})
  if pattern.search(code):code_hits.append({'file':n,'line':i,'text':raw})
assert pattern.search('sorry') and pattern.search('Lean.ofReduceBool') and pattern.search('debug.skipKernelTC')
report['proof_bypass_scan']={'pattern':pattern.pattern,'method':'Lexical scan after masking nested block comments, line comments, and string literals; raw matches retained for inspection.','raw_matches':raw_hits,'hits':code_hits};save()
assert not report['proof_bypass_scan']['hits']
print('Preflight PASS: fresh sources; all nine pinned revisions and tracked sources clean; Lean 4.19.0; no proof-bypass tokens.',flush=True)
t=time.monotonic();build=run([str(binpath/'lake'),'build']);(out/'build.txt').write_text(build.stdout);report['build']={'command':['lake','build'],'exit_code':build.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'log':'build.txt'};save()
assert build.returncode==0,build.stdout
print('Fresh lake build PASS',flush=True)
for n in sources:
 t=time.monotonic();cmd=[str(binpath/'lake'),'env','lean','-DwarningAsError=true',n];r=run(cmd)
 report['strict_replay'].append({'file':n,'command':['lake','env','lean','-DwarningAsError=true',n],'exit_code':r.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'output':r.stdout});save()
 if n=='Check.lean':(out/'axioms.txt').write_text(r.stdout)
 assert r.returncode==0,(n,r.stdout)
 print('Strict source replay PASS:',n,flush=True)
expected=[normalize_lean_name(n) for n in re.findall(r'^#print axioms ('+lean_name_pattern+r')\s*$',(dst/'Check.lean').read_text(),re.M)]
audit=(out/'axioms.txt').read_text()
actual=[]
for match in re.finditer(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$",audit,re.M):
 actual.append({'theorem':normalize_lean_name(match.group(1)),'axioms':[] if match.group(2) is None else [s.strip() for s in match.group(2).split(',') if s.strip()]})
allowed={'propext','Classical.choice','Quot.sound'}
report['axiom_audit']={'expected_count':expected_audit_count,'parsed_count':len(actual),'expected_theorems':expected,'audits':actual,'allowed_axioms':sorted(allowed),'all_names_match':expected==[a['theorem'] for a in actual],'only_allowed_axioms':all(set(a['axioms'])<=allowed for a in actual)};save()
assert len(expected)==len(actual)==expected_audit_count
assert report['axiom_audit']['all_names_match'] and report['axiom_audit']['only_allowed_axioms']
report['independent_sha256']={n:sha(dst/n) for n in sources+configs}
report['source_unchanged']=report['source_sha256']=={n:sha(src/n) for n in sources+configs}
report['copied_files_unchanged']=report['source_sha256']==report['independent_sha256']
assert report['source_unchanged'] and report['copied_files_unchanged']
assert sha(frozen_identity_path)==frozen_identity_sha256
report['frozen_identity_record']['record_unchanged_after']=True
report['frozen_identity_record']['source_hashes_match_after']=report['independent_sha256']==frozen_identity
assert report['frozen_identity_record']['source_hashes_match_after']
assert sha(inventory_path)==report['audit_inventory_sha256_before'], 'Inventory changed during verification'
assert expected==audit_names['theorems']
definitions=[normalize_lean_name(n) for n in re.findall(r'^#print (?!axioms )('+lean_name_pattern+r')\s*$',(dst/'Check.lean').read_text(),re.M)]
checked=[normalize_lean_name(n) for n in re.findall(r'^#check ('+lean_name_pattern+r')\s*$',(dst/'Check.lean').read_text(),re.M)]
report['definition_and_type_audit']={'definition_names':definitions,'definition_count':len(definitions),'checked_theorem_names':checked,'checked_theorem_count':len(checked),'checked_names_match_audits':checked==expected}
assert len(definitions)==expected_def_count and len(checked)==expected_audit_count and checked==expected
assert definitions==audit_names['definitions']
assert len(definitions)==sum(d['kind'] in {'def','abbrev','opaque','structure','class','inductive'} for d in audit_names['declarations'])
assert [d['name'] for d in audit_names['declarations'] if d['kind'] in {'theorem','lemma','instance'}]==expected
assert len(audit_names['instances'])==expected_instance_count and set(audit_names['instances'])<=set(expected)
assert sum(d['kind'] in {'theorem','lemma'} for d in audit_names['declarations'])==expected_theorem_count
assert sum(d['kind']=='instance' for d in audit_names['declarations'])==expected_instance_count
report['audit_inventory_sha256']=sha(inventory_path)
report['execution_audit_scope']='Fresh independent build and trust/identity verification; separate from the independent semantic review.'
report['axiom_audit']['theorem_lemma_count']=expected_theorem_count
report['axiom_audit']['named_instance_count']=expected_instance_count
report['axiom_audit']['zero_axiom_declarations']=[a['theorem'] for a in actual if not a['axioms']]
actual_defs=[normalize_lean_name(n) for n in re.findall(r'^(?:@\[[^\]]+\]\s+)*(?:def|theorem|opaque|abbrev|structure|class|inductive) ('+lean_name_pattern+r')',audit,re.M)]
actual_types=[normalize_lean_name(n) for n in re.findall(r'^('+lean_name_pattern+r')',audit,re.M) if normalize_lean_name(n) in checked]
d=report['definition_and_type_audit']
d.update({'printed_definition_names':actual_defs,'printed_definition_count':len(actual_defs),'printed_definition_names_match':actual_defs==definitions,'printed_theorem_type_names':actual_types,'printed_theorem_type_count':len(actual_types),'printed_theorem_type_names_match':actual_types==checked})
save()
assert len(actual_defs)==expected_def_count and actual_defs==definitions
assert len(actual_types)==expected_audit_count and actual_types==checked
for required in sorted(instance_names):
 assert source_instance_names.count(required)==1, 'Named instance source declaration must occur exactly once'
 assert audit_names['instances'].count(required)==1, 'Named instance inventory entry must occur exactly once'
 assert checked.count(required)==1 and actual_types.count(required)==1, 'Named instance type must be requested and actually emitted exactly once'
 assert expected.count(required)==1 and sum(a['theorem']==required for a in actual)==1, 'Named instance axioms must be requested and actually emitted exactly once'
report['named_instance_coverage'].update({'requested_and_emitted_type_once':True,'requested_and_emitted_axiom_audit_once':True,'actual_audits':[a for a in actual if a['theorem'] in instance_names]})
save()
# The authored-source inventory and Check transcript above are complemented by
# exhaustive enumeration of all constants originating in the compiled modules.
# This catches generated constructors, projections, recursors, equation lemmas,
# automatic instances and compiler runtime declarations without name guessing.
implementation_modules=[n[:-5].replace('/','.') for n in sources if n!='Check.lean']
harness_path=dst/'IndependentEnvironmentInventory.lean'
assert not harness_path.exists()
harness='\n'.join('import '+m for m in implementation_modules)+'\nimport Lean\n\n'
harness+='set_option pp.universes true\nset_option pp.fullNames true\n\n'
harness+="""set_option maxRecDepth 20000
set_option maxHeartbeats 0

open Lean
namespace IndependentTrustInspection

def deps (ci : ConstantInfo) : Array Name :=
  let body := match ci with
    | .defnInfo v => v.value.getUsedConstants
    | .thmInfo v => v.value.getUsedConstants
    | .opaqueInfo v => v.value.getUsedConstants
    | .inductInfo v => v.all.toArray ++ v.ctors.toArray
    | .recInfo v => v.all.toArray ++ v.rules.foldl (fun acc rule =>
        acc ++ #[rule.ctor] ++ rule.rhs.getUsedConstants) #[]
    | _ => #[]
  ci.type.getUsedConstants ++ body

partial def closure (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: todo =>
    if seen.contains n then closure env todo seen else
    let seen := seen.insert n
    match env.checked.get.find? n with
    | none => closure env todo seen
    | some ci => closure env ((deps ci).toList ++ todo) seen

run_elab do
  let env ← getEnv
"""
harness+='  let modules : Array Name := #['+', '.join('`'+m for m in implementation_modules)+']\n'
harness+='''  let mut count := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.allImportedModuleNames[idx.toNat]!
      if modules.contains moduleName then
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let typeText ← Meta.ppExpr ci.type
        let axioms ← collectAxioms name
        let reach := closure env [name]
        let unsafeReach := reach.toList.filter fun c =>
          (env.checked.get.find? c).any (·.isUnsafe)
        let partialReach := reach.toList.filter fun c =>
          (env.checked.get.find? c).any (·.isPartial)
        let missingReach := reach.toList.filter fun c => (env.checked.get.find? c).isNone
        let record := Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson moduleName.toString),
          ("kind", toJson kind),
          ("type", toJson typeText.pretty),
          ("unsafe", toJson ci.isUnsafe),
          ("partial", toJson ci.isPartial),
          ("axioms", toJson (axioms.map Name.toString)),
          ("direct_dependencies", toJson ((deps ci).map Name.toString)),
          ("closure_size", toJson reach.toList.length),
          ("unsafe_closure", toJson (unsafeReach.map Name.toString)),
          ("partial_closure", toJson (partialReach.map Name.toString)),
          ("missing_closure", toJson (missingReach.map Name.toString))]
        IO.println ("ENVDECL " ++ record.compress)
        count := count + 1
  IO.println ("ENVCOUNT " ++ toString count)
end IndependentTrustInspection
'''
harness_path.write_text(harness)
(out/'environment-inventory.lean').write_text(harness)
t=time.monotonic()
environment_result=run([str(binpath/'lake'),'env','lean','-DwarningAsError=true',harness_path.name])
(out/'environment-inventory.txt').write_text(environment_result.stdout)
environment_declarations=[]
environment_counts=[]
for line in environment_result.stdout.splitlines():
 if line.startswith('ENVDECL '):environment_declarations.append(json.loads(line[len('ENVDECL '):]))
 if line.startswith('ENVCOUNT '):environment_counts.append(int(line[len('ENVCOUNT '):]))
environment_names=[d['name'] for d in environment_declarations]
authored_names={d['name'] for d in source_declarations}
environment_by_name={d['name']:d for d in environment_declarations}
# Lean 4.19 compiler artifacts are retained in the complete inventory, but
# distinguished from logical declarations. Any explicitly classified unsafe axiom stubs below
# arise in eager lambda lifting and specialization (documented in the pinned
# compiler sources); they do not occur in any safe declaration's dependency
# closure. This exact allowlist is source-specific, not a blanket axiom waiver.
# Candidate-specific compiler stubs must be explicitly justified from this
# candidate's fresh output and the pinned compiler source before adding names.
compiler_stub_unsafe_closures = {'Con.lift._at.Conjecture637.exponentSum._spec_3': ['Con.lift._at.Conjecture637.exponentSum._spec_3'], 'Con.lift._at.Conjecture637.strandPermutation._spec_10': ['Con.lift._at.Conjecture637.strandPermutation._spec_10'], 'Con.liftOn._at.Conjecture637.strandPermutation._spec_11': ['Con.liftOn._at.Conjecture637.strandPermutation._spec_11'], 'Equiv.swap._at.Conjecture637.permutationGenerator._spec_1': ['Equiv.swap._at.Conjecture637.permutationGenerator._spec_1'], 'MonoidHom.ker._at.Conjecture637.pureBraidSubgroup._spec_1': ['MonoidHom.ker._at.Conjecture637.pureBraidSubgroup._spec_1'], 'MonoidHom.mker._at.Conjecture637.pureBraidSubgroup._spec_2': ['MonoidHom.mker._at.Conjecture637.pureBraidSubgroup._spec_2'], 'Nat.binaryRec._at.Conjecture637.fullTwist._spec_3': ['Nat.binaryRec._at.Conjecture637.fullTwist._spec_3'], 'PresentedGroup.toGroup._at.Conjecture637.exponentSum._spec_1': ['PresentedGroup.toGroup._at.Conjecture637.exponentSum._spec_1', 'lcProof'], 'PresentedGroup.toGroup._at.Conjecture637.strandPermutation._spec_1': ['PresentedGroup.toGroup._at.Conjecture637.strandPermutation._spec_1', 'lcProof'], 'Quotient.map₂._at.Conjecture637.halfTwist._spec_1': ['Quotient.map₂._at.Conjecture637.halfTwist._spec_1', 'QuotientGroup.con._at.Conjecture637.strandPermutation._spec_7', 'Subgroup.closure._at.Conjecture637.strandPermutation._spec_2', 'lcProof'], 'QuotientGroup.con._at.Conjecture637.strandPermutation._spec_7': ['QuotientGroup.con._at.Conjecture637.strandPermutation._spec_7'], 'QuotientGroup.leftRel._at.Conjecture637.strandPermutation._spec_8': ['QuotientGroup.leftRel._at.Conjecture637.strandPermutation._spec_8'], 'QuotientGroup.lift._at.Conjecture637.exponentSum._spec_2': ['QuotientGroup.lift._at.Conjecture637.exponentSum._spec_2', 'lcProof'], 'QuotientGroup.lift._at.Conjecture637.strandPermutation._spec_6': ['QuotientGroup.lift._at.Conjecture637.strandPermutation._spec_6', 'lcProof'], 'Singleton.singleton.«_@».Mathlib.Data.Set.Operations._hyg.22._at.Conjecture637.braidRelations._spec_1': ['Singleton.singleton.«_@».Mathlib.Data.Set.Operations._hyg.22._at.Conjecture637.braidRelations._spec_1'], 'Subgroup.closure._at.Conjecture637.strandPermutation._spec_2': ['Subgroup.closure._at.Conjecture637.strandPermutation._spec_2'], 'Subgroup.op._at.Conjecture637.strandPermutation._spec_9': ['Subgroup.op._at.Conjecture637.strandPermutation._spec_9'], 'Submonoid.comap._at.Conjecture637.pureBraidSubgroup._spec_3': ['Submonoid.comap._at.Conjecture637.pureBraidSubgroup._spec_3'], 'Submonoid.copy._at.Conjecture637.strandPermutation._spec_5': ['Submonoid.copy._at.Conjecture637.strandPermutation._spec_5'], 'iInf._at.Conjecture637.strandPermutation._spec_3': ['iInf._at.Conjecture637.strandPermutation._spec_3'], 'iInf._at.Conjecture637.strandPermutation._spec_4': ['iInf._at.Conjecture637.strandPermutation._spec_4'], 'npowBinRec._at.Conjecture637.fullTwist._spec_1': ['npowBinRec._at.Conjecture637.fullTwist._spec_1'], 'npowBinRec.go._at.Conjecture637.fullTwist._spec_2': ['npowBinRec.go._at.Conjecture637.fullTwist._spec_2']}
compiler_stub_names = set(compiler_stub_unsafe_closures)
assert not compiler_stub_names & authored_names
assert compiler_stub_names <= set(environment_by_name)
for name in compiler_stub_names:
 d = environment_by_name[name]
 assert d['unsafe'] and not d['partial'] and d['kind']=='axiom'
 assert d['axioms']==[name] and sorted(d['unsafe_closure'])==compiler_stub_unsafe_closures[name]
 assert not d['partial_closure'] and not d['missing_closure']
runtime_generated=[d for d in environment_declarations if d['unsafe'] and
 re.search(r'\._cstage[12]$',d['name']) and d['name'] not in authored_names and d['kind']=='definition']
runtime_names={d['name'] for d in runtime_generated} | compiler_stub_names
unexpected_unsafe=[d for d in environment_declarations if d['unsafe'] and d['name'] not in runtime_names]
logical_declarations=[d for d in environment_declarations if d['name'] not in runtime_names]
extra_names=sorted(set(environment_names)-authored_names)
environment_report={
 'method':'Enumerate imported environment constants by actual originating module; emit full type, declaration kind, safety flags and transitive collectAxioms result for every constant. No name-prefix filter or silent exclusion.',
 'command':['lake','env','lean','-DwarningAsError=true',harness_path.name],
 'exit_code':environment_result.returncode,
 'elapsed_seconds':round(time.monotonic()-t,3),
 'module_names':implementation_modules,
 'harness_sha256':sha(harness_path),
 'log':'environment-inventory.txt',
 'parsed_count':len(environment_declarations),
 'emitted_count_markers':environment_counts,
 'authored_count':len(authored_names),
 'all_authored_names_present':authored_names<=set(environment_names),
 'generated_or_additional_names':extra_names,
 'generated_or_additional_count':len(extra_names),
 'compiler_runtime_generated_names':sorted(runtime_names),
 'compiler_runtime_note':'All compiler artifacts retain their full types, axiom lists and closures. Known _cstage1/_cstage2 definitions and explicitly documented unsafe compiler axiom stubs are distinguished from the safe logical declarations; no logical dependency on either is permitted.',
 'compiler_unsafe_axiom_stub_names':sorted(compiler_stub_names),
 'compiler_stub_expected_unsafe_closures':compiler_stub_unsafe_closures,
 'compiler_stub_primary_sources': ['https://github.com/leanprover/lean4/blob/v4.19.0/src/Init/Prelude.lean#L129-L137', 'https://github.com/leanprover/lean4/blob/v4.19.0/src/library/compiler/specialize.cpp#L906-L920'],
 'logical_declaration_count':len(logical_declarations),
 'closure_audit_method':'Traverse every compiled declaration type and logical body transitively, including theorem bodies, mutual inductive declarations, constructors and recursor rules; record unsafe, partial and missing dependencies. Runtime compiler outputs remain explicitly inventoried; all other declarations must have empty issue lists.',
 'logical_closure_issues':[{'name':d['name'],'unsafe':d['unsafe_closure'],'partial':d['partial_closure'],'missing':d['missing_closure']} for d in environment_declarations if d['name'] not in runtime_names and (d['unsafe_closure'] or d['partial_closure'] or d['missing_closure'])],
 'unexpected_unsafe':unexpected_unsafe,
 'partial_declarations':[d['name'] for d in environment_declarations if d['partial']],
 'axiom_declarations':[d['name'] for d in logical_declarations if d['kind']=='axiom'],
 'all_inventory_axiom_declarations':[d['name'] for d in environment_declarations if d['kind']=='axiom'],
 'only_allowed_axioms':all(set(d['axioms'])<=allowed for d in logical_declarations),
 'standard_axiom_check_scope':'Every safe logical declaration, including all authored declarations and generated logical declarations. Runtime artifacts are individually recorded and excluded from every logical dependency closure.',
 'declarations':sorted(environment_declarations,key=lambda d:d['name']),
}
report['complete_environment_audit']=environment_report
(out/'environment-inventory.json').write_text(json.dumps(environment_report,indent=2)+'\n')
save()
assert environment_result.returncode==0,environment_result.stdout
assert environment_counts==[len(environment_declarations)] and environment_declarations
assert len(environment_names)==len(set(environment_names)), 'Duplicate environment declaration output'
assert authored_names<=set(environment_names), sorted(authored_names-set(environment_names))
assert all(d['module'] in implementation_modules for d in environment_declarations)
assert len(environment_declarations)==194 and len(logical_declarations)==81 and len(runtime_generated)==90 and len(compiler_stub_names)==23
assert not unexpected_unsafe and not environment_report['partial_declarations']
assert not environment_report['axiom_declarations'] and environment_report['only_allowed_axioms']
assert not environment_report['logical_closure_issues'], environment_report['logical_closure_issues']
for d in source_declarations:
 actual_declaration=environment_by_name[d['name']]
 assert actual_declaration['module']==d['file'][:-5].replace('/','.'),d
 assert not actual_declaration['unsafe'] and not actual_declaration['partial'],d
 assert actual_declaration['type'].strip(),d
 if d['kind'] in {'theorem','lemma'}:assert actual_declaration['kind']=='theorem',d
 if d['kind'] in {'structure','class','inductive'}:assert actual_declaration['kind']=='inductive',d
 if d['kind'] in {'def','abbrev'}:assert actual_declaration['kind']=='definition',d
 if d['kind']=='opaque':assert actual_declaration['kind']=='opaque',d
# Check every explicit theorem/instance audit against the independent environment
# collection, rather than trusting a transcript parser alone.
assert all(set(a['axioms'])==set(environment_by_name[a['theorem']]['axioms']) for a in actual)
print(f'Complete environment audit PASS: {len(environment_declarations)} declarations, including {len(extra_names)} generated/additional constants.',flush=True)
assert report['source_sha256']=={n:sha(src/n) for n in sources+configs}
assert report['source_sha256']=={n:sha(dst/n) for n in sources+configs}
assert sha(inventory_path)==report['audit_inventory_sha256_before']
assert sha(frozen_identity_path)==frozen_identity_sha256
assert sha(pathlib.Path(__file__))==report['verifier_sha256']
post=[]
for d in report['dependencies']:
 a=run(['git','status','--porcelain','--untracked-files=no'],pkgs/d['name'])
 h=run(['git','rev-parse','HEAD'],pkgs/d['name'])
 post.append({'name':d['name'],'status_command':['git','status','--porcelain','--untracked-files=no'],'exit_code':a.returncode,'tracked_status':a.stdout,'tracked_clean':a.returncode==0 and not a.stdout,'head_command':['git','rev-parse','HEAD'],'head_exit_code':h.returncode,'actual_rev':h.stdout.strip(),'revision_matches':h.returncode==0 and h.stdout.strip()==d['expected_rev']})
report['dependencies_post_build']=post
assert all(d['tracked_clean'] and d['revision_matches'] for d in post)
compiler_after=run([str(binpath/'lean'),'--githash'])
report['lean_commit_post_build']={'exit_code':compiler_after.returncode,'actual':compiler_after.stdout.strip(),'unchanged':compiler_after.returncode==0 and compiler_after.stdout.strip()==report['lean_commit']['expected']}
assert report['lean_commit_post_build']['unchanged']
version_after=run([str(binpath/'lean'),'--version'])
report['lean_version_post_build']={'exit_code':version_after.returncode,'output':version_after.stdout.strip(),'unchanged':version_after.returncode==0 and version_after.stdout.strip()==report['lean_version']['output']}
assert report['lean_version_post_build']['unchanged']
report['source_unchanged_after_all_audits']=report['source_sha256']=={n:sha(src/n) for n in sources+configs}
report['copied_files_unchanged_after_all_audits']=report['source_sha256']=={n:sha(dst/n) for n in sources+configs}
assert report['source_unchanged_after_all_audits'] and report['copied_files_unchanged_after_all_audits']
assert sha(frozen_identity_path)==frozen_identity_sha256
assert sha(inventory_path)==report['audit_inventory_sha256_before']
assert sha(pathlib.Path(__file__))==report['verifier_sha256']
report['execution_record_file']='execution-records.json';report['execution_record_sha256']=sha(out/'execution-records.json')
report['status']='PASS';report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
print(f'All {expected_audit_count} named audits PASS ({expected_theorem_count} theorems,{expected_instance_count} instances), with {expected_def_count} printed definitions/abbreviations/structures. Only standard axioms; source/config and inventory hashes unchanged.',flush=True)
print(json.dumps(report['source_sha256'],indent=2),flush=True)
