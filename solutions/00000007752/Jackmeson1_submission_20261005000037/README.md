# Disprove conjecture 00000007752: the Böttcher coordinate of z^2-2 is algebraic, so phi_c(z)/z is not always transcendental

The conjecture says that for every algebraic `c` with `0` non-escaping, `phi_c(z)/z` is transcendental at every algebraic `z` of large modulus. It adds an algebraic-independence clause for `phi_{c1}/phi_{c2}`.

**Witness.** Take `c = -2`, i.e. `z^2 - 2`. Its critical orbit `0 -> -2 -> 2 -> 2` is bounded. Its Böttcher coordinate is `psi(z) = (z + z·sqrt(1-4/z^2))/2`, the root of `w^2 - z w + 1` of modulus greater than 1. The square root is the branch asymptotic to `z` at infinity. At algebraic `z`, both `psi(z)` and `psi(z)/z` are algebraic. The monomial case `c = 0`, `phi = id`, is also formalized.

**Normalization.** The text omits `phi(z)/z -> 1`, so both readings are handled:
- (N) Normalized: a rigidity lemma (if `G o f = G^2` and `G -> 1`, then `G = 1` near infinity) shows that every such `phi` equals `psi` near infinity.
- (U) Unnormalized but meromorphic at infinity: `1/psi` is also a solution, so the coordinate is not unique. Every solution equals `0` or `psi^m` near infinity.

In every case the values at large algebraic `z` are algebraic. So clause 1 fails whether it is read with "every" or "some" coordinate, and under both readings of "non-escaping" (orbit bounded, or orbit not tending to infinity). Clause 2 fails as well: `z/psi(z)` is algebraic (take `c1 = 0`, `c2 = -2`).

**Lean.** `C7752.conjecture_7752_false` is stated with Mathlib's `IsAlgebraic`, `Transcendental`, `AnalyticOnNhd`, `MeromorphicAt` and `cobounded`. The file is 482 lines and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It compiles with `-DwarningAsError=true`.

**Scope.** `c = 0` and `c = -2` are the classical explicit cases (`z^2 - 2 = 2·T_2(z/2)`), and the statement includes them ("every algebraic c"). The unnormalized reading is formalized under meromorphy at infinity. The variant with no condition at infinity is covered by a mathematical remark only: univalence excludes an essential singularity.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7752/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007752.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7752.conjecture_7752_false`, `C7752.clause2_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007752 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
