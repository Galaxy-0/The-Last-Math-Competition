# Prove conjecture 00000002511: symmetric tensors correspond to homogeneous polynomials, multiplicatively

- **Setting.** A field K of characteristic 0 and V with a finite basis b (n variables); V^{⊗d} is Mathlib's `PiTensorProduct`, and symmetric tensors are those fixed by every permutation of the factors (`PiTensorProduct.reindex`). Classical result (Comon–Golub–Lim–Mourrain, arXiv 0802.1681 §3.1; Wikipedia "Symmetric tensor" — retrieved, quotes checked), re-proved in Lean.
- **Dictionary.** `toPoly`: v₁⊗…⊗v_d ↦ ℓ(v₁)…ℓ(v_d) with ℓ(b_j) = X_j; `eval_toPoly` shows it is T ↦ (φ ↦ T(φ,…,φ)) in coordinates.
- **Symmetric tensors are forms.** Every d-tensor maps into `MvPolynomial.homogeneousSubmodule ι K d`.
- **Isomorphism.** On symmetric tensors the dictionary is a linear isomorphism `symEquiv : Sym^d V ≃ₗ K[X]_d` (injective via content fibres and characteristic 0; surjective via symmetrized monomial tensors); hence the two spaces have equal dimension.
- **Closure under products.** T ⊙ U = Sym(T ⊗ U) (averaging convention) maps to the product of forms, and p·q corresponds to the symmetric product of the preimages.
- **Not covered.** Positive characteristic, other normalizations of ⊙, and the explicit dimension formula C(n+d−1, d); "closes under homogeneous polynomials" is read as closure under products.
- **Main theorem.** `C2511.symmetric_tensors_are_forms`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 341 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2511/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002511.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2511.symmetric_tensors_are_forms`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002511 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
