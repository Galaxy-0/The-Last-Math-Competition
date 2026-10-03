'use strict';
// Independent recursive generation of partitions; not used by the Lean proof.
const assert = require('node:assert/strict');
function partitions(total, largest = total) {
  if (total === 0) return [[]];
  const result = [];
  for (let first = Math.min(total, largest); first >= 1; --first) {
    for (const tail of partitions(total - first, first)) result.push([first, ...tail]);
  }
  return result;
}
function rank(parts) { return parts[0] - parts.length; }
function crank(parts) {
  const ones = parts.filter(x => x === 1).length;
  return ones === 0 ? parts[0] : parts.filter(x => x > ones).length - ones;
}
const all = partitions(4);
assert.deepEqual(all, [[4], [3, 1], [2, 2], [2, 1, 1], [1, 1, 1, 1]]);
assert.deepEqual(all.map(rank), [3, 1, 0, -1, -3]);
assert.deepEqual(all.map(crank), [4, 0, 2, -2, -4]);
assert.equal(all.filter(p => rank(p) === 4).length, 0);
assert.equal(all.filter(p => crank(p) === 4).length, 1);
console.log(JSON.stringify({ partitions: all, ranks: all.map(rank),
  cranks: all.map(crank), rankFourCount: 0, crankFourCount: 1 }, null, 2));
