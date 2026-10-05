# Disprove conjecture 00000002181: sensitivity is not bounded by √2·log n times the spectral norm

The conjecture claims s(f) ≤ √2 · log n · ‖f̂‖₁ for every Boolean function on n variables (conjoined with an undefined clause about "pointer maxima of real hypercubical faces"). Parity on n bits is a counterexample for every n ≥ 2:
- **Sensitivity.** Flipping any bit flips parity, so its sensitivity is n at every input (maximum = average = n).
- **Spectral norm.** Its Fourier spectrum is a single character: spectral norm 1 with ±1 output, and 1 with 0/1 output.
- **Comparison.** √2 ln n < n and √2 log₂ n < n for all n ≥ 1 (e.g. n = 2: 2 > 1.414).
- **Stronger.** C·log n·‖f̂‖₁ < s(f) for all large n, for every constant C (any log base), and the failure persists inside linear threshold functions (AND: s = n, spectral norm ≤ 3 / = 1; `and_no_log_bound`).
- **Main theorem.** `C2181.conjecture_2181_false` (both log bases, both encodings), with `parity_violates`, `no_log_bound`.
- **Scope.** Only the first clause is refuted; the second is undefined. Under a truth-table-size reading n = 2^k, parity still refutes the bound with the natural log (√2·ln 2·k < k); only the base-2 variant of that reading (√2·k ≥ k) is not refuted.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 443 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** A submission by orionsheep for this conjecture (PR #179) was merged and then removed in the full re-audit (commit 541cf4fb). The re-audit's reason: "(1:Nat) = 1 := rfl posing as sensitivity". Its Lean defined no Boolean function, no sensitivity and no Fourier coefficients, so nothing about the conjecture was formalized. This submission defines Boolean functions on n bits, sensitivity and the normalised Fourier l1 norm in Lean, for both the ±1 and the 0/1 encodings. It proves that parity violates the bound for every n ≥ 2, under both log bases and for every constant C.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2181/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002181.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2181.conjecture_2181_false`, `C2181.parity_violates`, `C2181.no_log_bound`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002181 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
