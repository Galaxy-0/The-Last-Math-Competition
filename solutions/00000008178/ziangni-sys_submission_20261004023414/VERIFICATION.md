# Verification evidence

Verified on 2026-10-04 with Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Formal statement and correspondence

`radical n` is the product of `Nat.primeFactors n`, not an assumed radical
value. `ABCTriple a b c` asserts positivity, `a < b`, the equation `a+b=c`,
and all three pairwise coprimality conditions. `ABCHit` adds the strict
inequality `radical (a*b*c) < c`. `CutoffHit` further requires the real
inequality `radical (a*b*c) <= c^(1-epsilon)`.

`IsSmallestHit c0` is the necessary minimum condition that every ABC hit
has `c0 <= c`. The cutoff version restricts this universal quantifier to
the stated epsilon class. Refuting a necessary minimum condition refutes
the proposed minimum without assuming it is a hit.

`counterexample` proves a positive epsilon below one, the full cutoff hit
`(3,125,128)`, `128 < 23^5`, and both minimum negations. The proof thus
disproves the conjecture's smallest-hit clause, not its density or
algorithm-complexity clauses.

## Lean checks

Commands run from the `lean` directory with the pinned toolchain:

```text
lake build
lake env lean Main.lean
```

Results: both commands exited with code 0. The local project build directory
was initially absent; Mathlib dependency artifacts came from its matching
pinned cache. The build printed `Built Main` and `Build completed successfully.`
The direct file check prints the final theorem audit:

```text
'ABC8178.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard logical foundations. No proof depends on `sorryAx`,
an additional axiom, or `native_decide`. Prime factors are established
using Mathlib's multiplication and prime-power factorization theorems;
finite arithmetic and coprimality are kernel checked. The real power
inequality is proved through `Real.rpow_le_rpow_iff` and `Real.rpow_mul`.

## Report checks

`tectonic -X compile report.tex` succeeds and produces a two-page PDF.
Both pages were rendered with Poppler and visually inspected for complete
content, readable formulas, and absence of clipping or overlap. The final
Tectonic run had no overfull/underfull box warnings. Tectonic printed a
nonfatal Fontconfig configuration diagnostic; embedded Latin Modern fonts
rendered correctly. The built-in editor compiler was also attempted but
returned its platform-directory lookup failure, so the actual PDF was
compiled with Tectonic.

No numerical approximation, external computation, or auxiliary script is
needed for the mathematical argument.
