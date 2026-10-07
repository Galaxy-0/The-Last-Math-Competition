# Disprove conjecture 00000009629: the full 2-shift and full 4-shift have order-isomorphic dimension groups but are not orbit equivalent

- **Claim refuted.** The "if" direction of the first clause ("two mixing SFTs are orbit equivalent iff their dimension groups are order-isomorphic"), hence the conjunction; the entropy and Kakutani–Rokhlin clauses are not addressed.
- **Witnesses.** The edge shifts X_[2], X_[4] of the 1×1 matrices [2], [4] (full shifts on 2 and 4 symbols), built as Mathlib `Subshift`s; both are SFTs (Mathlib `forbidden`) and topologically mixing (proved).
- **Dimension groups.** Krieger's dimension group in the eventual-range model (Schmieding, arXiv:1803.04060 §2, retrieved and quoted): G_A = {x ∈ R(A) : xA^k ∈ ℤ^r for some k} with cone from (ℤ₊)^r; for [2] and [4] both equal ℤ[1/2] with its usual cone, so the identity is an order isomorphism.
- **Not orbit equivalent.** Any bijection mapping orbits into orbits — in particular any orbit-preserving Borel isomorphism, as in the Definition line — sends fixed points to fixed points under its inverse; X_[4] has 4 fixed points and X_[2] has 2 (`no_orbit_map`). This also rules out topological orbit equivalence.
- **Not refuted.** "Dimension groups" read as the dimension triple (with the shift automorphism), or as the Giordano–Putnam–Skau group K⁰(X,T); SFTs are taken as edge shifts with the dimension group of the presenting matrix.
- **Main theorems.** `C9629.counterexample`, `C9629.not_OEDimCriterion`, `C9629.conjecture_false`, `C9629.no_orbit_map`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 381 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture9629/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000009629.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C9629.counterexample`, `C9629.not_OEDimCriterion`, `C9629.conjecture_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-06): no solution folder for 00000009629 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
