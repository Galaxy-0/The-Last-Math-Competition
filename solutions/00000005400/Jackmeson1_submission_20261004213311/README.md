# Disprove conjecture 00000005400: conjugate maps cannot have different periods

The conjecture needs three things:

- two maps with identical orbit-distribution limits and different periodic-point counts;
- that separation realized by **an explicit conjugate pair with the same measure but different periods**.

The last clause can never hold. Let `h` be a bijection with `h ∘ f = g ∘ h`. Then `h` maps the `n`-periodic points, the points of least period `n` and the `n`-cycles of `f` bijectively onto those of `g`. The two maps have the same period sets, and `h` preserves the least period at every point (`minimalPeriod_eq`).

This holds for every map on every space; the counts are cardinals. It also holds no matter what "identical orbit distribution limits" and "same measure" mean, since the Lean statement takes both as arbitrary predicates. Homeomorphic and measure-preserving conjugacies are special cases and get their own corollaries. The conjunction is therefore false.

**History.** An earlier submission for this conjecture (PR #25) was merged and later removed with the note "#5400: refuted a mechanism/reading, not the literal statement". That submission only enumerated permutations of a 4-point set. This one refutes the literal final clause for all maps on all spaces. It uses the same conjugacy-invariance argument as the accepted solution of the near-duplicate 00000005390, which is credited (GPL-3.0). The report also explains why "conjugate" is read pointwise, as a bijection intertwining the maps everywhere, and not modulo null sets.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture5400/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000005400.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture5400.conjecture5400_false`, `Conjecture5400.conjecture5400_samePair_false`, `Conjecture5400.homeomorph_conjugate_same_periods`, `Conjecture5400.measured_conjugate_same_periods`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000005400 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
