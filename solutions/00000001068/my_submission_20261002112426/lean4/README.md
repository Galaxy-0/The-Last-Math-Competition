# Lean 4 formalization — Disproof of TLMC conjecture 00000001068

Pure core Lean 4 (no Mathlib, no dependencies). `Main.lean` formalizes the
counterexample `p = 11` to the conjecture "the maximal sum-free subsets of
`F_p` are exactly the intervals `((p+1)/3, 2(p-1)/3)` up to dilation":

- `A = {4,5,6,7}` is sum-free in `F_11` (`A_sum_free`) and maximal
  (`A_maximal`), with `|A| = 4` (`A_size`).
- The conjectured interval is exactly `{5,6}` (`interval_eq`), size `2`
  (`interval_size`), strictly contained in `A` (`interval_subset_A`,
  `interval_not_maximal`) — hence not maximal.
- Every nonzero dilate of the interval is strictly contained in a sum-free
  dilate of `A` (`dilates_of_interval_not_maximal`) and still has two
  elements (`dilates_of_interval_size_2`), so no dilate of the interval is
  maximal, and the 4-element maximal set `A` is not a dilate of it.
- `disproof` packages the whole counterexample.

All proofs are `rfl` on closed `Bool` computations.

## Build and verify

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints the axiom profile of every theorem; each line must read
"does not depend on any axioms" (zero axioms, zero `sorry`).
