"""Materialize only the versions in dependencies.lock.json; never update existing revisions.
Run with Python 3 after installing the official version in lean-toolchain.
"""
from pathlib import Path
import json,subprocess
root=Path(__file__).resolve().parent
lock=json.loads((root/'dependencies.lock.json').read_text(encoding='utf-8'))
def git(dest,*args):
 return subprocess.run(['git','-C',str(dest),*args],check=True,capture_output=True,text=True,timeout=120).stdout.strip()
packages=[dict(lock['mathlib'],name='mathlib'),*lock['packages']]
for package in packages:
 dest=root/'.lake/packages'/package['name']
 if (dest/'.git').exists():
  actual=git(dest,'rev-parse','HEAD')
  if actual!=package['rev']:raise SystemExit(f'Revision mismatch in {dest}: {actual}; left untouched')
  if git(dest,'status','--porcelain','--untracked-files=no'):raise SystemExit(f'Modified dependency {dest}; left untouched')
  print('Verified existing',package['name'],actual)
  continue
 if dest.exists() and any(dest.iterdir()):raise SystemExit(f'Nonempty unmanaged directory: {dest}; left untouched')
 dest.mkdir(parents=True,exist_ok=True)
 git(dest,'init');git(dest,'remote','add','origin',package['url'])
 git(dest,'fetch','--depth','1','origin',package['rev'])
 git(dest,'checkout','--detach','FETCH_HEAD')
 assert git(dest,'rev-parse','HEAD')==package['rev']
 print('Materialized',package['name'],package['rev'])
print('Pinned dependency sources ready. Use lake exe cache get with the modules in README.md; do not run lake update.')
