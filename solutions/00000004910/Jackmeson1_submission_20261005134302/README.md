# Prove conjecture 00000004910: merging duplicate actions gives two MDPs with identical optimal policies and value functions but different transitions

The conjecture asks for two MDPs with identical optimal policies and value functions but different transition structures, realized by merging redundant actions. We read "redundant" as exact duplicates (same law and reward) and "merging" as identifying them into one action.
- **General theorem.** Take an MDP whose actions in each fibre of a map `q` are duplicates, and let `quot M g` merge each fibre into one action. The pushforward `push` of a history-dependent randomized policy plays the conditional law of the merged action given the merged history.
  - The merged history process of `π` has exactly the law of `push π` (`law_push`), so values agree (`discValue_push`).
  - `push (lift π') = π'`, so `push` is onto (`push_lift`).
  - For every β: V* is equal (`optValue_quot`), and `π` is optimal iff `push π` is (`isOptimal_push`).
  - So Opt(M) = push⁻¹(Opt(M')) and Opt(M') = push(Opt(M)).
- **Witness.** States Bool. `M₂` has actions `opt` (reward 1, stay) and duplicates `red₁`, `red₂` (reward 0, switch). `M₃ = quot M₂ rep` has actions `opt`, `red`.
  - `M₂`'s kernel is not injective in the action. `M₃`'s is.
  - V* = 1/(1−β) in both (β < 1). `constPol opt` is optimal in both.
- **Main theorem.** `Conjecture4910.conjecture4910`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 370 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4910/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004910.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture4910.conjecture4910`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004910 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
