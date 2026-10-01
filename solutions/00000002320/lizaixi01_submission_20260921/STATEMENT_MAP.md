# Mathematical note: TLMC 00000002320

## Fixed target

Source at upstream commit `95acb520ec5607c826b8a997b1ef2fc82d6f7c57`:

> Conjecture: The spectrum of the probability P(G) of uniformly random generating pairs over all finite groups is an explicit dense subsequence of [1/4, 1]; the subsequence is realized by the PSL(2,p) family (P → 1/4 as p → ∞).

Source URL: <https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/95acb520ec5607c826b8a997b1ef2fc82d6f7c57/conjectures/00000002320.md>.

The necessary consequence to disprove is `P(G) >= 1/4` for every finite group G. The source imposes neither simplicity nor two-generation. The separate asserted limit along PSL(2,p) is not needed for the counterexample and is not the target of this formalization.

## Standard probability definition

For a finite group G, define

`N_2(G) = #{(a,b) in G × G : <a,b> = G}`,

and

`P(G) = N_2(G) / |G|^2`.

This is the probability for two independent uniformly distributed group elements, with replacement. It counts ordered pairs. Igor Pak's *On probability of generating a finite group* (December 30, 1999), page 3, gives this standard k-tuple definition. Author-hosted primary source: <https://www.math.ucla.edu/~pak/papers/sim.pdf>.

All such probabilities are rational. The Lean source represents them exactly in Q; the same zero value and strict comparison hold under the usual embedding into R. No numerical approximation is involved.

## Counterexample and proof

Let G = (Z/2Z)^3 under coordinatewise addition, equivalently the elementary abelian multiplicative group of order 8.

For any a,b in G, commutativity and a+a=b+b=0 imply that every word in a and b lies in the set

`H(a,b) = {0,a,b,a+b}`.

More explicitly, this set contains zero and is closed under addition and inverses, so it is a subgroup containing a and b. It has at most 4 elements, whereas G has 8. Therefore `<a,b>` is a proper subgroup of G for every pair.

There are 8^2 = 64 ordered pairs and no generating pair. Consequently

`P(G) = 0/64 = 0 < 1/4`.

Hence the spectrum over all finite groups is not a subset of [1/4,1], so it cannot be the asserted dense subsequence. This disproves the full conjecture through a necessary consequence.

## Formal correspondence

The source `lean/Results/Counterexample2320.lean` uses:

- `G := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)`, a genuine mathlib group.
- `inFour a b x`: the predicate `x=1 or x=a or x=b or x=a*b`.
- `fourSubgroup`: the actual subgroup with that carrier, with multiplication and inverse closure proved by finite kernel computation.
- `four_misses_element`: a finite kernel proof that for every pair some group element is absent from that subgroup.
- `pair_closure_le_four`: the actual `Subgroup.closure` is contained in the constructed subgroup.
- `no_pair_generates`: the actual generated subgroup is never top.
- `generatingPairs`: the finite set of all ordered pairs whose `Subgroup.closure` is top.
- `generatingPairProbability`: the corresponding cardinality ratio, defined for arbitrary finite groups.
- `generatingPairs_empty`, `generatingPairProbability_zero`, and `conjectureInterval_false`: the count, probability, and contradiction.

The `decide` checks certify concrete finite group operations and existence of a missing element. They do not replace generation with a custom false predicate. No `native_decide` is used.

## Attribution and limits

This is an elementary established fact about elementary abelian groups, used to expose a false universal statement. No mathematical novelty is claimed. The repository's complete 100-PR title/body snapshot checked at 2026-09-20T17:13:39Z had no matching problem identifier. That supports only the statement that no matching submission was found by this bounded check; it does not establish world-first discovery or priority.

Compilation and axiom-audit status must be read from the attempt ledger and final root validation, not inferred from this explanatory note.
