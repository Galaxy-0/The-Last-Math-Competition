# Prove conjecture 00000003526: for ordinal trees, no descending chains ⟺ well-founded, and the well-founded rank is the ordinal height

- **Trees.** Descriptive-set-theory trees: nonempty prefix-closed sets of finite sequences over any type (in particular over the ordinals); well-founded = no branch (Wikipedia's definition, retrieved).
- **Equivalences.** No branch ⟺ no infinite descending chain of proper extensions (via f(k) = c_{k+1}(k)) ⟺ the strict-extension relation `Ext` is well-founded (descending-chain criterion, dependent choice) ⟺ an order-reversing ordinal ranking exists.
- **Rank.** ρ_T satisfies ρ(s) = sup{ρ(s⌢a) + 1}, is its unique solution, and is the least order-reversing map into the ordinals.
- **Height.** The ordinal height, defined independently as the least bound of a ranking, equals sup{ρ(s) + 1} = ρ(∅) + 1 (arXiv:1201.5495, retrieved: "the rank (also called the ordinal height)").
- **Realization and set-theoretic trees.** Every ordinal α is realized (the tree of strictly decreasing sequences below α has ρ(∅) = α, height α + 1); for set-theoretic trees, < is well-founded, each node's rank equals its height, and the tree's height is sup(rank + 1).
- **Scope.** A classical, nearly definitional fact; every definition is written out and each equivalence proved from it. Under the sup(ρ+1) convention heights of nonempty trees are successor ordinals (stated). Other meanings of "tree lemma" (Kőnig's lemma, large-cardinal tree properties) and the "partitions" part of the Definition line are not covered.
- **Main theorems.** `C3526.tree_wf_rank_height`, `C3526.ordinal_tree_realization`, `C3526.setTree_wf_rank_height`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 383 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3526/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003526.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3526.tree_wf_rank_height`, `C3526.ordinal_tree_realization`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003526 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
