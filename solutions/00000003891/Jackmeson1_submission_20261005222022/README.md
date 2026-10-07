# Disprove conjecture 00000003891: the Witt ghost inverse problem is not well posed in any standard reading

- **Object.** Mathlib's p-typical Witt vectors with ghost components w_n = Σ_{i≤n} pⁱ x_i^{p^{n−i}} (`WittVector.ghostComponent`, `ghost_formula`); ghost sequences live in the compact space ℤ_p^ℕ (product topology), for every prime p.
- **Reading A (components in ℤ_p).** (0,1,0,…) has no preimage (x₀ = 0 forces p·x₁ = 1), so "always a unique solution" fails (`e1_not_ghost`).
- **Reading B (components in ℚ_p).** Unique solvability holds (`ghostEquiv`), but if ‖w₁ − w₀^p‖ = 1 then v(x_n) = −(pⁿ − 1)/(p − 1) for all n ≥ 1 (`norm_comps`); the nonempty open set {‖w₁ − w₀^p‖ = 1} lies in the unbounded-valuation set, so that set has nonzero measure for every measure positive on open sets, in particular every Haar measure (`measure_ne_zero`, `haar_ne_zero`): not measure zero.
- **Reading C ("unbounded above").** ghost(1,…,1,p^k,p^{k+1},…) → ghost(1,1,1,…), whose components all have valuation 0, so the set is not closed in ℤ_p^ℕ nor in the ghost image of W(ℤ_p) (`not_closed`, `not_closed_in`).
- **Literal printed formula.** For Σ x_i^{pⁱ}, (0,p,0,…) needs x₁^p = p, impossible in ℚ_p (`lit_no_solution`). Mathlib's `valuation 0 = 0` convention is never used.
- **Not covered.** Ghost sequences in the non-compact ℚ_p^ℕ; the degenerate reading "integral components, unbounded below" (empty set); the Haar measure on the product is used only through positivity on open sets.
- **Main theorem.** `C3891.main_theorem`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 411 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3891/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003891.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3891.main_theorem`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003891 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
