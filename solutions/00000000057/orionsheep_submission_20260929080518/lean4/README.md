# Lean 4 formalization — disproof of TLMC conjecture 00000000057

Core Lean only (no Mathlib), toolchain `leanprover/lean4:v4.33.1`.

Contents of `Main.lean`:

- `part` / `adj` — the counterexample family `G_k` (disjoint union of `k`
  copies of `K_{3,3}`) on vertices `0 .. 6k-1`.
- `IsCycle` — simple cycles (length ≥ 3, pairwise distinct vertices, cyclic
  adjacency).
- `edge_flip` / `step_flip` / `cycle_even` — every cycle has even length
  (adjacency flips the bipartition side; a closed walk returns to its side
  only after an even number of steps).
- `IsPrime` / `even_not_prime` / `no_prime_cycles` — even length ≥ 3 is at
  least 4, hence composite; so no cycle of `G_k` has prime length.
- `adj_oppL` / `adj_oppR` / `three_neighbors` — every vertex has three
  pairwise distinct neighbors (minimum degree 3).
- `log2_ge_one` / `disproof_00000000057` — the family witnesses the failure:
  0 distinct prime cycle lengths for every `k`, while
  `log₂ n ≥ 1` on the whole family (`n = 6k ≥ 6`) and
  `log₂ 6 / log₂ (log₂ 6 + 1) = 2`.

Zero `sorry`, zero axioms — verified by `Check.lean` (`#print axioms`).

## Build

```
export ELAN_HOME=/Users/mychanging/.workbuddy-ai/binaries/lean/elan
export PATH="$ELAN_HOME/bin:$PATH"
lake build
lake env lean Check.lean
```

Expected output: nine `#'disproof_00000000057' does not depend on any axioms`
lines (one per audited declaration).
