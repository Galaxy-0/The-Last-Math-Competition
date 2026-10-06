# Prove conjecture 00000004780: swapping the diagonal blocks keeps every joint moment but changes the M_2(C)-valued distribution

The conjecture asks for two matrix models whose joint moments have identical asymptotics but whose operator-valued distributions differ, with the separation realized by an explicit rearrangement of the block structure.
- **Models.** `X_N = (A ⊗ 1_N, C ⊗ 1_N)` in `M_2(M_N(C))`, with `A = diag(1,0)` and `C = [[0,1],[1,0]]`. `Y` is `X` with its two diagonal blocks swapped, i.e. conjugated by `σ ⊗ 1_N` for `σ = (0 1)` (`rearrange`). All four matrices are self-adjoint.
- **Joint moments.** `tr_{2N}(p(X_N)) = tr_{2N}(p(Y_N))` for every `N` and every noncommutative polynomial `p` (`FreeAlgebra`). Both sequences converge to `tr_2(p(A,C))`. The general lemma `rearrange_jointMoment` covers every model and every block permutation.
- **Operator-valued distributions.** With `B = M_2(C)` and `E_N = id_2 ⊗ tr_N`, the first B-valued moment is `diag(1,0)` for `X` and `diag(0,1)` for `Y`, for every `N ≥ 1` and in the limit. In general a rearrangement conjugates the B-valued moments by `σ` (`rearrange_condExp`).
- **Main theorem.** `Conjecture4780.conjecture4780`.
- **Caveat.** The witnesses are deterministic (constant random matrices) of the form `a ⊗ 1_N`. The statement does not ask for randomness.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 248 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4780/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004780.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture4780.conjecture4780`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004780 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
