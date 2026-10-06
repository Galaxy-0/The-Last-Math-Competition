"""Read-only validation of pinned standard package revisions and tracked trees."""
import hashlib, json, pathlib, subprocess
project=pathlib.Path('/private/tmp/tlmc545-proof')
pinned=json.loads((project/'pinned-dependencies.json').read_text())
for package in pinned['packages']:
    path=project/'.lake/packages'/package['name']
    sha=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
    tracked=subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True)
    assert sha==package['rev'], (package['name'],sha,package['rev'])
    assert not tracked, (package['name'],tracked)
    print(package['name'],sha,'TRACKED_TREE_UNCHANGED')
for name in ['lean-toolchain','lake-manifest.json','pinned-dependencies.json']:
    print(name,hashlib.sha256((project/name).read_bytes()).hexdigest())
print('ALL_PINNED_PACKAGES_PASS')
