// Independent exact finite verification. This is not a Lean proof oracle.
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const assert = require('assert/strict');
const E = [0, 1, 2, 3, 4];
const le = (x, y) => x === 0 || y === 4 || x === y;
const meet = (x, y) => x === 4 ? y : y === 4 ? x : x === y ? x : 0;
const join = (x, y) => x === 0 ? y : y === 0 ? x : x === y ? x : 4;
const rank = x => x === 0 ? 0 : x === 4 ? 2 : 1;
const cover = (x, y) => le(x, y) && x !== y &&
  E.every(z => !le(x, z) || !le(z, y) || z === x || z === y);
const subsets = Array.from({length: 32}, (_, m) => E.filter(x => m & (1 << x)));
const chain = a => a.every(x => a.every(y => le(x, y) || le(y, x)));
const anti = a => a.every(x => a.every(y => !le(x, y) || x === y));
const included = (a, b) => a.every(x => b.includes(x));
for (const x of E) {
  assert(le(x, x) && le(0, x) && le(x, 4));
  assert.equal(E.filter(a => cover(0, a) && le(a, x)).reduce(join, 0), x);
  for (const y of E) {
    if (le(x, y) && le(y, x)) assert.equal(x, y);
    assert(le(meet(x, y), x) && le(meet(x, y), y));
    assert(le(x, join(x, y)) && le(y, join(x, y)));
    if (cover(x, y)) assert.equal(rank(y), rank(x) + 1);
    if (cover(meet(x, y), x)) assert(cover(y, join(x, y)));
    for (const z of E) {
      if (le(x, y) && le(y, z)) assert(le(x, z));
      if (le(z, x) && le(z, y)) assert(le(z, meet(x, y)));
      if (le(x, z) && le(y, z)) assert(le(join(x, y), z));
    }
  }
}
const chains = subsets.filter(chain);
const antichains = subsets.filter(anti);
const ranks = [0, 1, 2].map(r => E.filter(x => rank(x) === r));
assert.deepEqual(ranks.map(a => a.length), [1, 3, 1]);
assert.deepEqual(antichains.filter(a => a.length === 3), [[1, 2, 3]]);
const familyMaxima = [0, 1, 2, 3].map(k =>
  Math.max(...subsets.filter(a => chains.every(c => !included(c, a) || c.length <= k)).map(a => a.length)));
assert.deepEqual(familyMaxima, [0, 3, 4, 5]);
// Independently use the union-of-antichains convention as well.
const unionOfTwoMaximum = Math.max(...antichains.flatMap(a => antichains.map(b => new Set([...a, ...b]).size)));
assert.equal(unionOfTwoMaximum, 4);
const mu = [];
for (const x of E) mu[x] = x === 0 ? 1 : -E.filter(y => y !== x && le(y, x)).reduce((s, y) => s + mu[y], 0);
assert.deepEqual(mu, [1, -1, -1, -1, 2]);
const coefficients = [0, 1, 2].map(k => E.filter(x => 2 - rank(x) === k).reduce((s, x) => s + mu[x], 0));
assert.deepEqual(coefficients, [2, -3, 1]);
const result = {
  totalElements: E.length, totalSubsets: subsets.length,
  chainsIncludingEmpty: chains.length, antichainsIncludingEmpty: antichains.length,
  rankSizes: ranks.map(a => a.length), kFamilyMaximaForK0Through3: familyMaxima,
  unionOfTwoAntichainsMaximum: unionOfTwoMaximum,
  mobius: mu, characteristicCoefficientsAscending: coefficients,
  checkedAt: new Date().toISOString(),
  sha256: Object.fromEntries(['lean/Main.lean', 'main.tex', 'SOURCE.md'].map(f =>
    [f, crypto.createHash('sha256').update(fs.readFileSync(path.join(__dirname, f))).digest('hex')]))
};
fs.writeFileSync(path.join(__dirname, 'auxiliary-verification.json'), JSON.stringify(result, null, 2) + '\n');
console.log(JSON.stringify(result, null, 2));
