# Disproof of conjecture `00000002476`

**Verdict: FALSE — the Glaisher merging map does not preserve part
counts: (3,3) ↦ (6) sends a 2-part partition to a 1-part partition.**

## The conjecture (verbatim from `conjectures/00000002476.md`)

> Definition: Glaisher's theorem: odd parts versus distinct parts.
> Conjecture: The Glaisher correspondence is the explicit bijection
> merging repeated parts into odd parts; the merging map preserves part
> counts, giving equinumerous families.

## Object consistency

We use the standard Glaisher correspondence between partitions into odd
parts and partitions into distinct parts: group equal parts, write each
group's multiplicity m in binary, and replace the group of m equal
parts p by the distinct parts p·2^i over the set bits i of m. This is
the textbook map (Andrews, *The Theory of Partitions*, Ch. 1). We attack
the displayed claim "the merging map preserves part counts" about this
exact map.

## The counterexamples

* **(3,3) ↦ (6).** The partition (3,3) of 6 has two equal odd parts
  (multiplicity 2 = 10₂, set bit i = 1); the group is replaced by the
  single part 3·2 = 6. Part count: **2 → 1.** Both sides partition 6,
  and (3,3) is into odd parts while (6) is into distinct parts, so this
  is exactly a Glaisher pair.
* **(1,1,1) ↦ (2,1).** Multiplicity 3 = 11₂ → parts 1·1 and 1·2. Part
  count: **3 → 2.**
* **(2,2,2,2) ↦ (8).** Multiplicity 4 = 100₂ → part 2·4 = 8. Part
  count: **4 → 1.**

So "preserves part counts, giving equinumerous families" is false: the
Glaisher correspondence is a bijection between the SETS of partitions
(it preserves the integer being partitioned), not between the graded
families by number of parts. (Indeed the classical refinement result is
that Glaisher maps "k parts" to "at most ... " — it does not fix the
part count.)

## Verification

* `reproduce.py` — implements the full Glaisher map from the textbook
  definition, runs it over ALL partitions of n = 1..40, and reports
  every partition whose image changes the part count (hundreds of
  examples; the smallest is (1,1) ↦ (2), a 2 → 1 pair), plus the three
  counterexamples above.
* Lean 4 (core, v4.33.1) — `lean4/`: the map is defined by the textbook
  rule; kernel computations certify G([3,3]) = [6], G([1,1,1]) = [2,1],
  G([2,2,2,2]) = [8], G([6]) = [6] (involution on the pair), the sums
  (6 = 6, 3 = 3, 8 = 8), and the part-count mismatches 2 ≠ 1, 3 ≠ 2,
  4 ≠ 1. All 8 audited theorems report `does not depend on any axioms`.

## Boundary

Only the "merging map preserves part counts" clause is refuted; the
existence of the Glaisher bijection itself (odd parts ↔ distinct parts)
is of course true and is not disputed.
