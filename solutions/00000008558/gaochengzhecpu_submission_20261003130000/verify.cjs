// Independent complete finite checks; not a Lean proof oracle.
const fs=require('fs'),path=require('path'),crypto=require('crypto'),assert=require('assert/strict');
const E=[0,1,2],meet=Math.min,join=Math.max;
const embeddings=[];
for (let n=0;n<=2;n++) {
  const B=Array.from({length:2**n},(_,x)=>x), maps=[];
  for (const a of B) for (const b of B) for (const c of B) {
    const f=[a,b,c];
    if (new Set(f).size!==3) continue;
    if (E.every(x=>E.every(y=>f[meet(x,y)]===(f[x]&f[y])&&f[join(x,y)]===(f[x]|f[y])))) maps.push(f);
  }
  embeddings.push({dimension:n,totalMaps:B.length**3,embeddings:maps});
}
assert.deepEqual(embeddings.map(x=>x.embeddings.length),[0,0,2]);
assert(embeddings[2].embeddings.some(f=>JSON.stringify(f)==='[0,1,3]'));
const closure=(s,bounded)=>{
  const reached=new Set(s);
  if (bounded) { reached.add(0);reached.add(2); }
  let changed=true;
  while (changed) {
    const before=reached.size;
    for (const x of [...reached]) for (const y of [...reached]) { reached.add(meet(x,y));reached.add(join(x,y)); }
    changed=reached.size!==before;
  }
  return [...reached].sort();
};
const subsets=Array.from({length:8},(_,m)=>E.filter(x=>m&(1<<x)));
const generators=subsets.filter(s=>closure(s,false).length===3);
const boundedGenerators=subsets.filter(s=>closure(s,true).length===3);
assert.deepEqual(generators,[[0,1,2]]);
assert.equal(Math.min(...generators.map(s=>s.length)),3);
assert.equal(Math.min(...boundedGenerators.map(s=>s.length)),1);
assert(boundedGenerators.every(s=>s.includes(1)));
const result={
  checkedAt:new Date().toISOString(),embeddings,
  allSubsets:subsets.map(s=>({set:s,ordinaryClosure:closure(s,false),boundedClosure:closure(s,true)})),
  minimumBooleanDimension:2,minimumOrdinaryGenerators:3,minimumBoundedGenerators:1,
  sha256:Object.fromEntries(['lean/Main.lean','main.tex','SOURCE.md'].map(f=>
    [f,crypto.createHash('sha256').update(fs.readFileSync(path.join(__dirname,f))).digest('hex')]))
};
fs.writeFileSync(path.join(__dirname,'auxiliary-verification.json'),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result,null,2));
