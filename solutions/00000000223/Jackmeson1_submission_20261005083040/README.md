# Disprove conjecture 00000000223: for each prime q the density of n with q | E_n is 0, not of q^{-2} type

For a fixed prime q = p_{r+1}, q divides p_n# for every n > r, so q never divides E_n = p_n# + 1 afterwards (Euclid's argument). Hence {n : q | E_n} ⊆ [0, r] is finite and has natural density 0.
- **Definitions.** p_n# is the product of the first n primes via `Nat.nth Nat.Prime` (not Mathlib's `primorial`, which multiplies the primes ≤ n). Natural density on ℕ.
- **Results.** Every prime q has density 0, and no prime has a nonzero density. The exact reading (density = c/q², c ≠ 0) is false; it already fails at q = 2. The asymptotic reading (q²·d(q) → c ≠ 0, i.e. d(q) ~ c·q^{-2}) is false.
- **Main theorem.** `C223.conjecture_223_density_clause_false`.
- **Scope.** This refutes the last clause and with it the conjunction. A pure "O(q^{-2})" upper-bound reading is not refuted: "an explicit value of q^{-2} type" is read as a nonzero value. The least-prime-factor and log-scale clauses are not addressed.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 129 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture223/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000223.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C223.conjecture_223_density_clause_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000223 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
