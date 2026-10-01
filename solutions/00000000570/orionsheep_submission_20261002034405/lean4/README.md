# Lean 4 verification package (conjecture 00000000570, verdict FALSE)

Core Lean 4 only — no Mathlib, no external dependencies, zero axioms,
zero `sorry`.

## What is proved

* `relz2 … relz8`: the seven Kronecker exchange relations
  xₙ₋₁ · xₙ₊₁ = xₙ² + 1 (n = 2 … 8) hold coefficientwise for the term
  tables `TBL1 … TBL9` — the Laurent expansions of the first nine cluster
  variables of the Kronecker cluster algebra (rank 2, exchange matrix
  [[0,2],[-2,0]], affine Ã₁, acyclic) in the initial cluster (x₁, x₂).
* `width3 … width9`: the x₁-exponent of the support of xₙ lies in the strip
  [-(n-2), n-4] and both endpoints are attained (`coeffOf TBL6 (-4,-3) ≠ 0`,
  `coeffOf TBL6 (2,-3) ≠ 0`, …), so the support widths are exactly
  0, 2, 4, 6, 8, 10, 12 for n = 3 … 9.
* `disproof_00000000570`: packages everything — in particular width 6 > 4
  (x₆) and width 12 > 4 (x₉), violating the conjectured bound 2·rank = 4.

## Build

```
lake build
lake env lean Check.lean
```

Every `#print axioms` line must print "does not depend on any axioms".

Style note: `decide` is used only on closed propositions; `omega`, `simp`
and `native_decide` are avoided (the former two may pull in
`propext`/`Quot.sound`); open-goal reasoning is term-mode `Eq`/`congrArg`
composition with case analysis on `List.Mem`.
