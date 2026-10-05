# Disprove conjecture 00000000591: the Wilf surplus/Frobenius ratio does not tend to 0 in embedding dimension 3

- **Family.** S_k = ⟨6, 12k+10, 18k+15⟩ (k ≥ 0), numerical semigroups (`AddSubmonoid.closure` in ℕ) with minimal generators exactly {6, 12k+10, 18k+15}, so embedding dimension 3.
- **Apéry set.** A membership characterization with respect to 6 (`mem_S_iff`) is proved in Lean for every k, giving F(S_k) = 42k+29 (Mathlib `FrobeniusNumber`), n(S_k) = genus = 21k+15 (via the symmetry x ↦ F−x), and surplus e·n − F − e = 21k+13.
- **Consequence.** surplus/F ≥ 1/3 for all k while F → ∞, refuting the limit and any explicit rate (`not_ratioTendsToZero`). With g read as the genus, (e·n − g − e)/g ≥ 1, so that reading fails too (`not_genusRatioTendsToZero`).
- **Scope.** Embedding dimension is defined as the number of atoms; that atoms are the unique minimal generating system is not proved in general.
- **Main theorems.** `C591.not_ratioTendsToZero`, `C591.not_genusRatioTendsToZero`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 262 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PRs #132 and #169 by orionsheep, both closed without merging, used the family S_k = <6, 2(6k+5), 3(6k+5)>. In #132 the Lean proved only four isolated instances with g <= 603, and the reviewer noted that "finite data cannot refute a limit statement". In #169 the limit statement was formalized, but in the reviewer's words "frob/surplus are still definitions, anchored to the actual semigroups <6, 2(6k+5), 3(6k+5)> only by exhaustive checks at k = 0 and k = 1"; the reviewer asked for "a general membership/characterization proof in Lean (e.g. an Apery-set computation for the family)". This submission supplies that. It defines S_k as `AddSubmonoid.closure {6, 12k+10, 18k+15}` and proves the Apery-set membership characterization for every k. From it, again for every k, it derives the numerical-semigroup property, the minimal generators {6, 12k+10, 18k+15} (so e = 3), the Frobenius number 42k+29 in the sense of Mathlib's `FrobeniusNumber`, n(S_k) = genus = 21k+15, and surplus 21k+13. It then proves in Lean that the ratio does not tend to 0, under both the Frobenius reading and the genus reading of g.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture591/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000591.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C591.not_ratioTendsToZero`, `C591.not_genusRatioTendsToZero`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000591 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
