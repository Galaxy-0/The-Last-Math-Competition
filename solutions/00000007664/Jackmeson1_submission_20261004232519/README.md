# Disprove conjecture 00000007664: 9 Gamma_q(3/2) + 8 Gamma_q(-1/2) = 0 at q = 1/4, so the pair is algebraically dependent

The conjecture claims that for every algebraic q in (0,1) and all distinct positive integers m, n with m/n != 1/2, the values Gamma_q(m/n) and Gamma_q(1-m/n) are algebraically independent over Q(q).

**Counterexample.** Take q = 1/4 (so Q(q) = Q), m = 3 and n = 2. Then m/n = 3/2 and 1 - m/n = -1/2, and neither value is a pole. The product identity (q^{-1/2};q)_inf = (1-q^{-1/2})(1-q^{1/2})(q^{3/2};q)_inf gives 9 Gamma_q(3/2) + 8 Gamma_q(-1/2) = 0. So the nonzero polynomial 9X + 8Y vanishes at the pair.

**Non-degeneracy.** Every product converges: the partial products decrease and are bounded below by the Weierstrass bound. Both denominators are nonzero, and Gamma_q(3/2) > 0 > Gamma_q(-1/2).

**Lean.** (a;q)_inf is defined as the limit of partial products, and Gamma_q is defined exactly as stated, using Real.rpow. Independence is Mathlib's AlgebraicIndependent over IntermediateField.adjoin ℚ {q}. The main theorem is `C7664.conjecture_00000007664_false : ¬ Conjecture`; a further theorem, `counterexample_values_genuine`, covers the non-degeneracy facts. Both use only the axioms propext, Classical.choice and Quot.sound.

**Scope.** The counterexample has m > n, which the statement permits ("any two distinct positive integers"). The case m < n, which the author may have intended, is an open transcendence question and is not addressed here.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7664/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007664.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7664.conjecture_00000007664_false`, `C7664.counterexample_values_genuine`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000007664 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
