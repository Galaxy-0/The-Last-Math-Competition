# Disprove conjecture 00000004053: the trivial F₃[C₃]-module has syzygy period 2, but 2 divides no prime factor of any defect group order

Counterexample: p = 3, G = C₃, k = F₃, M = the trivial F₃[C₃]-module.
- **Group algebra.** In Mathlib's `MonoidAlgebra (ZMod 3) (Multiplicative (ZMod 3))` with t = g − 1: t³ = 0, t² ≠ 0, and ker(augmentation) = tA.
- **Projective covers.** For a cyclic module M = A·m₀ with m₀ ∉ tM, every projective cover P → M (P projective, kernel superfluous) has P ≅ A and kernel = ann(m₀).
- **Period.** Ωk = ker ε = (t), Ω²k = ann(t) = (t²) ≅ k, and (t) ≇ k (t acts nontrivially on it). So the minimal period of k is 2, for every choice of covers. k is finitely generated, simple (hence indecomposable) and not projective.
- **Defect groups.** Every subgroup D of C₃ has order 1 or 3, so 2 divides neither |D| nor any prime factor of |D|. A defect group is such a subgroup, so the first clause fails (both the "q | r for a prime factor r of |D|" and the "q | |D|" readings).
- **Main theorems.** `conjecture_4053_false : ¬ Clause1 3 G`, `conjecture_4053_false'`, `trivial_module_counterexample`.
- **Scope.** The defect group is replaced by an arbitrary subgroup (a weaker formal clause, so a stronger refutation). Clause 2 ("admissible prime", "explicit block") is undefined and not needed for the conjunction.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 449 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #291 for this conjecture was closed without merging, with the label `lean_vacuous`. Its reviewer found that "the entire modular representation theory lives in the comments". The Lean main theorem was arithmetic about numerals and defined no group algebra, no module, no projective cover, no syzygy and no subgroup. This submission formalizes those objects. It uses Mathlib's group algebra F₃[C₃], the trivial module, projective covers with superfluous kernels, and syzygies as a relation. It computes Ωk ≅ (t) ≇ k and Ω²k ≅ k for every choice of covers, so the period is 2, and it quantifies over all subgroups of C₃.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4053/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004053.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C4053.conjecture_4053_false`, `C4053.trivial_module_counterexample`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004053 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
