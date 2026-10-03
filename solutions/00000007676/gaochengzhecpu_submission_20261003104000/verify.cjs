'use strict';
// Independent enumeration of all bijections of {1,2}.
const assert = require('node:assert/strict');
const permutations = [];
for (let a = 1; a <= 2; ++a) for (let b = 1; b <= 2; ++b) {
  if (a !== b) permutations.push([a, b]);
}
function statistics(p) {
  const descents = [];
  for (let i = 0; i + 1 < p.length; ++i) if (p[i] > p[i + 1]) descents.push(i + 1);
  return { major: descents.reduce((a, b) => a + b, 0), des: descents.length };
}
function A(q, t) {
  return permutations.reduce((sum, p) => {
    const s = statistics(p);
    return sum + q ** s.major * t ** s.des;
  }, 0);
}
assert.deepEqual(permutations, [[1, 2], [2, 1]]);
assert.deepEqual(permutations.map(statistics), [{major: 0, des: 0}, {major: 1, des: 1}]);
assert.equal(A(2, 0), 1);
assert.equal(A(2, 1), 3);
assert.notEqual(A(2, 1), 2 * A(2, 0));
console.log(JSON.stringify({permutations, statistics: permutations.map(statistics),
  A_2_0: A(2, 0), A_2_1: A(2, 1), gammaForcedAtZero: 1,
  gammaPredictionAtOne: 2, contradiction: '3 != 2'}, null, 2));
