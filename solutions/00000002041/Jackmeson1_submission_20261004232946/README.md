# Disprove conjecture 00000002041: {1} ∪ 4ℕ⁺ has density 1/4 but its subset sums miss every n ≡ 2, 3 (mod 4)

The conjecture claims that every set of density `≥ 0.24` is a complete sequence "covering minimally". The definition is garbled: the summand of `Σ_{a∈A, a≤n} ≥ n` is missing. We formalize the usual universal reading of the displayed definition together with the standard completeness notions; one witness refutes all of the enumerated readings. One variant is excluded: the eventual summand-`a` condition (only for large `n`). Every positive-density set satisfies it, including `A` itself for `n ≥ 8`, so under that variant the 0.24 threshold would say nothing.

**Witness.** Take `A = {1} ∪ {4k : k ≥ 1}`.
- **Density.** `|A ∩ [1,n]| = 1 + ⌊n/4⌋`, so natural, lower and upper density are all 1/4. Schnirelmann density (Mathlib's `schnirelmannDensity`) is at least 1/4. Every reading gives at least 0.24.
- **Missing sums.** Every sum of distinct elements of `A` is `≡ 0` or `1 (mod 4)`, so 2 and every `4N+2` cannot be represented.
- **Completeness fails.** `A` is not complete, not eventually complete and not minimal complete. It contains no complete, minimal complete or eventually complete subset.
- **The stated `Σ` condition fails** at `n = 2` under either summand: `Σ_{a≤2} a = 1 < 2`, and `#{a ≤ 2} = 1 < 2`.

**Lean.** `C2041.conjecture_2041_false` covers all 4 density readings × 8 completeness readings, each conjoined with an arbitrary second clause. A supplement, `no_threshold`, uses `ℕ \ {2}` (density 1, not complete) to show that no threshold `θ ≤ 1` works, including `1 - 1/e`. The file is 269 lines, uses only the axioms `propext`, `Classical.choice` and `Quot.sound`, and compiles with `-DwarningAsError=true`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2041/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002041.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2041.conjecture_2041_false`, `C2041.no_threshold`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000002041 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
