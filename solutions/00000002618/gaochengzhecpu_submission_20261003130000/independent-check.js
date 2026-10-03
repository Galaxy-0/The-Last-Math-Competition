"use strict";
// Independent enumeration by literal subset masks, not by Lean's operation definitions.
const elements = [0, 1, 2, 3, 4, 5, 7];
const le = (a, b) => (a & b) === a;
function join(S) {
  const upper = elements.filter(y => S.every(x => le(x, y)));
  return upper.find(y => upper.every(z => le(y, z)));
}
function meet(x, y) {
  const lower = elements.filter(z => le(z, x) && le(z, y));
  return lower.find(t => lower.every(z => le(z, t)));
}
const subsets = Array.from({length: 128}, (_, m) =>
  elements.filter((x, i) => (m >> i) & 1));
const rows = elements.map(w => {
  const reps = subsets.filter(S => join(S) === w);
  const irredundant = reps.filter(S => !reps.some(T =>
    T.length < S.length && T.every(x => S.includes(x))));
  const canonical = irredundant.filter(S =>
    irredundant.every(T => S.every(x => T.some(y => le(x, y)))));
  return {elementMask: w, joinRepresentations: reps.length,
    irredundantRepresentations: irredundant, canonicalRepresentations: canonical};
});
const meetFailures = [], joinFailures = [];
for (const x of elements) for (const y of elements) for (const z of elements) {
  if (meet(x, y) === meet(x, z) && meet(x, join([y, z])) !== meet(x, y))
    meetFailures.push([x, y, z]);
  if (join([x, y]) === join([x, z]) &&
      join([x, meet(y, z)]) !== join([x, y]))
    joinFailures.push([x, y, z]);
}
const result = {
  model: "B3 minus {b,c}; raw subset masks",
  elements, subsets: subsets.length,
  allSubsetsHaveJoin: subsets.every(S => join(S) !== undefined),
  rows, joinSemidistributivityFailures: joinFailures,
  meetSemidistributivityFailures: meetFailures,
  formalCodeCanonicalMasks: [0, 2, 4, 6, 16, 18, 20]
};
if (!result.allSubsetsHaveJoin || rows.some(r => r.canonicalRepresentations.length !== 1) ||
    joinFailures.length !== 0 || meetFailures.length !== 2)
  throw new Error("The independent verification did not match the asserted counterexample.");
process.stdout.write(JSON.stringify(result, null, 2) + "\n");
