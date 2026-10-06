# Disprove conjecture 00000004124: the least size of a ccc, non-Knaster poset is ℵ₁ or undefined, never ℵ₂

- **Claim refuted.** The first conjunct: "the least cardinality of a poset separating ccc from the Knaster property is ℵ₂". This refutes the conjunction; the Suslin-tree clause is not needed.
- **Definitions.** Compatible = having a common lower bound; ccc = every antichain is countable; Knaster = every uncountable subset has an uncountable pairwise-compatible subset. Knaster ⇒ ccc is proved, so "separating" means ccc and not Knaster.
- **Key lemma (`exists_aleph_one`).** If P is ccc and not Knaster, take an ℵ₁-sized W with no uncountable linked subset and close it under a chosen common-lower-bound function; the closure Q has size exactly ℵ₁, and compatibility in Q equals compatibility in P, so Q is ccc and not Knaster.
- **Lower bound.** Countable posets are vacuously Knaster, so every ccc, non-Knaster poset has size ≥ ℵ₁.
- **Conclusion.** The set S of such sizes is empty (no least element; Lean's sInf ∅ = 0, a stated convention) or has least element ℵ₁. Both `IsLeast S ℵ₂` and `sInf S = ℵ₂` are refuted for partial orders, preorders, and partial orders with a top, in any universe — in every model of ZFC, independently of MA_ℵ₁ or Suslin trees.
- **Sources (retrieved).** Wikipedia (Countable chain condition, Martin's axiom, Suslin tree) and Peng, arXiv:2510.21496. Readings requiring separative posets or complete Boolean algebras are not covered.
- **Main theorem.** `Conjecture4124.conjecture4124_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 278 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4124/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004124.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture4124.conjecture4124_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004124 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
