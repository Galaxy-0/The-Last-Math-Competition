// Independent exact enumeration, not a Lean proof oracle.
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const assert = require('assert/strict');
const points = [0, 1, 2];
const rel = (r, x, y) => Boolean(r & (1 << (3*x+y)));
const equiv = r => points.every(x => rel(r,x,x)) &&
  points.every(x => points.every(y => !rel(r,x,y) || rel(r,y,x))) &&
  points.every(x => points.every(y => points.every(z => !rel(r,x,y) || !rel(r,y,z) || rel(r,x,z))));
const valid = Array.from({length:512}, (_,r) => r).filter(equiv);
assert.deepEqual(valid, [273,283,341,433,511]);
// A second enumeration generates blocks directly from all color assignments.
const byBlocks = new Set();
for (const a of points) for (const b of points) for (const c of points) {
  const color = [a,b,c];
  let r = 0;
  for (const x of points) for (const y of points) if (color[x] === color[y]) r |= 1 << (3*x+y);
  byBlocks.add(r);
}
assert.deepEqual([...byBlocks].sort((a,b)=>a-b), valid);
const labels = [0,1,2,3,4];
const refines = (x,y) => points.every(i => points.every(j => !rel(valid[x],i,j) || rel(valid[y],i,j)));
for (const x of labels) for (const y of labels)
  assert.equal(refines(x,y), x===0 || y===4 || x===y);
const subsets = Array.from({length:32}, (_,m) => labels.filter(x => m & (1<<x)));
const chain = a => a.every(x => a.every(y => refines(x,y) || refines(y,x)));
const included = (a,b) => a.every(x=>b.includes(x));
const maximal = a => chain(a) && subsets.every(b => !chain(b) || !included(a,b) || included(b,a));
const maximalCodes = subsets.map((a,m)=>maximal(a)?m:-1).filter(m=>m>=0);
assert.deepEqual(maximalCodes,[19,21,25]);
const maximalLengths = maximalCodes.map(m=>subsets[m].length-1);
assert.deepEqual(maximalLengths,[2,2,2]);
const blocks = r => {
  const remaining = new Set(points), result=[];
  while (remaining.size) {
    const x = [...remaining][0];
    const block = points.filter(y=>rel(r,x,y));
    result.push(block);
    block.forEach(y=>remaining.delete(y));
  }
  return result;
};
const result = {
  totalRelationsChecked:512,
  equivalenceRelations:valid,
  partitionsAsBlocks:valid.map(blocks),
  totalPartitionFamiliesChecked:32,
  chainCountIncludingEmpty:subsets.filter(chain).length,
  maximalChainCodes:maximalCodes,
  maximalChainPartitionCodes:maximalCodes.map(m=>subsets[m].map(x=>valid[x])),
  maximalChainLengths:maximalLengths,
  checkedAt:new Date().toISOString(),
  sha256:Object.fromEntries(['lean/Main.lean','main.tex','SOURCE.md'].map(f=>
    [f,crypto.createHash('sha256').update(fs.readFileSync(path.join(__dirname,f))).digest('hex')]))
};
fs.writeFileSync(path.join(__dirname,'auxiliary-verification.json'),JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(result,null,2));
