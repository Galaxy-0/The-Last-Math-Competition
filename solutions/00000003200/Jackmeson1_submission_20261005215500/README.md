# Prove conjecture 00000003200: maximal regular sequences have length equal to the Ext-depth (Rees)

- **Reading.** For a Noetherian ring R, an ideal J and a finitely generated module M with JM ≠ M, every maximal M-regular sequence in J has length min{i : Ext^i(R/J, M) ≠ 0}; this minimum is finite and equals the supremum (indeed the maximum) of regular-sequence lengths.
- **Graded instances.** On S = k[x₁..x_m]: grade I = depth_I(S) for any proper ideal I (`grade_reading`), and the depth of S/I at the irrelevant ideal (Ext from the residue field k) for proper homogeneous I (`quotient_reading`).
- **Mathlib reuse.** The key equivalence (Ext vanishing below n ⇔ a regular sequence of length n in J) is Mathlib's `Rees.lean` (Nailin Guan), credited. New here: the extension lemma via the Ext long exact sequence, existence of a maximal sequence from Noetherianity, the equality of sup and min, and the graded instances.
- **Conventions.** Mathlib's `IsRegular` (so M ≠ (rs)M is part of the definition); "Ext = 0" means `Subsingleton`; sequences need not be homogeneous. Source: Wikipedia "Depth (ring theory)" (retrieved).
- **Not claimed.** Homogeneous regular sequences, the depth of I as a module, depth = dim.
- **Main theorem.** `C3200.rees_depth`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 257 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3200/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003200.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3200.rees_depth`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003200 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
