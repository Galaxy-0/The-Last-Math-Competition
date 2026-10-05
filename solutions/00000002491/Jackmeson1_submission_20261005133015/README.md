# Disprove conjecture 00000002491: Möbius values of the partition lattice do not vanish at partitions with repeated block sizes

The conjecture says the Möbius function of the partition lattice vanishes at partitions with repeated block sizes. In Π₄, σ = {12|34} has two blocks of size 2, yet μ(0̂, σ) = 1.
- **Lean objects.** Mathlib's `Finpartition (univ : Finset (Fin 4))` with its refinement order, and Mathlib's `IncidenceAlgebra.mu`.
- **Interval.** Lean proves that the interval [0̂, σ] is exactly {0̂, {12|3|4}, {1|2|34}, σ}, by a proof over all partitions below σ (`le_sigma_cases`), not a `decide` over Π₄.
- **Value.** The Möbius recursion gives μ(0̂, σ) = −(1 − 1 − 1) = 1 (`mu_bot_sigma`). The dual reading also fails: μ(σ, 1̂) = −1 (`mu_sigma_top`).
- **Scope.** The vague "inversion formula closes" clause is not formalized; the integer-partition (dominance order) reading is refuted in prose only.
- **Main theorems.** `C2491.conjecture_2491_false`, `C2491.conjecture_2491_false_dual`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 317 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** A submission by orionsheep for this conjecture (PR #191) was closed without merging. The reviewer's reason: "muAux runs on a hardcoded 4×4 Boolean matrix with no partitions and no partition lattice defined in Lean; the identification with the interval [0̂, σ] exists only in comments, and the padding theorem (2 = 2 : Bool) confirms no conjecture object is formalized." This submission formalizes the partition lattice Π₄ as Mathlib's `Finpartition (univ : Finset (Fin 4))` with its refinement order, uses Mathlib's Möbius function `IncidenceAlgebra.mu`, and defines "has a repeated block size" on partitions. It proves in Lean that every x ≤ σ = {01|23} is one of four explicit partitions, computes μ(0̂, σ) = 1 and μ(σ, 1̂) = −1, and concludes that μ does not vanish on all partitions with repeated block sizes (`conjecture_2491_false`, `conjecture_2491_false_dual`). It also corrects a prose slip of the earlier text: Π₄ has six partitions of type (2,1,1), not two.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2491/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002491.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2491.conjecture_2491_false`, `C2491.conjecture_2491_false_dual`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002491 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
