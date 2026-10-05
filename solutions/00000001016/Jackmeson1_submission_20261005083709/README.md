# Prove conjecture 00000001016: no binary self-dual [84,12] code exists

For the nondegenerate standard dot product on F₂ⁿ, dim C + dim C^⊥ = n, so a self-dual code (C = C^⊥) has dimension n/2, which is 42 for n = 84.
- **Main claim.** No binary self-dual [84,12,12] code exists, extremal or not. This proves the conjecture's main claim outright.
- **Other claims.** The universal claims about self-dual [84,12] codes (no automorphism of order 11, minimum distance ≤ 11) hold vacuously, because the class is empty.
- **Definitions.** Subspaces of `Fin 84 → ZMod 2`, the orthogonal complement for the dot product (`LinearMap.BilinForm.finrank_orthogonal`), Hamming-weight minimum distance via Mathlib `hammingNorm`, coordinate-permutation automorphisms.
- **Reading.** The statement asserts no existence; the Definition only calls the code a "candidate". Under a nonstandard "self-orthogonal" reading, the padded triple Golay [84,12,24] code would break the d ≤ 11 claim; we use C = C^⊥.
- **Main theorem.** `C1016.conjecture_1016`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 107 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1016/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001016.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1016.conjecture_1016`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001016 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
