# Disprove conjecture 00000000741: x^2 never has exactly three periodic points mod p, so n(p) = 3 holds for no prime

The conjecture says three things:
- for a density-one set of primes, n(p) = 3, where n(p) is the number of periodic points of f(x) = x^2 on Z_p, named as the fixed points 0, 1 and -1;
- the exceptional primes number at most x^{1/2+eps};
- the exceptions are characterized by large power factors of p^2 - 1.

**Key fact.** In any integral domain, the squaring map never has exactly three periodic points. Suppose the periodic set were {0, 1, x}. Then x is a unit, and its inverse is also periodic, so x^{-1} = x and x = -1. But (-1)^(2^k) = 1, so -1 is periodic only when -1 = 1. Hence n(p) != 3 for every prime p, both for Z/pZ and for the p-adic integers. In fact n(p) = 1 + (odd part of p - 1), which is always even.

**First clause fails.** No prime has n(p) = 3, so that set of primes is empty. Its relative prime-counting ratio is identically 0, so it cannot be a density-one set, and the conjunction fails whatever the other clauses mean. The Lean proves this for an arbitrary proposition `Q` standing for the other clauses.

**Also proved.** The fixed points of x^2 on Z/pZ are exactly {0, 1}, and -1 is not periodic for odd p. So "the fixed points 0, 1 and -1" never occur.

**Lean.** `Conjecture741.conjecture_00000000741_false` uses Mathlib's `Function.periodicPts`, `ZMod p`, `ℤ_[p]` and `Nat.primeCounting'`. It relies only on the axioms propext, Classical.choice and Quot.sound, with no sorry and no native_decide.

**Reading.** n(p) counts periodic points; the Chinese text states this explicitly (计相异周期轨道点). The report also explains, in prose only, why an orbit-count reading of the English parenthesis fails too: primes p ≡ 1 (mod 7) have at least four orbits.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture741/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000741.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture741.conjecture_00000000741_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000000741 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
