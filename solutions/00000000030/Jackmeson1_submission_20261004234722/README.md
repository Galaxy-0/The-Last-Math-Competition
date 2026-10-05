# Disprove conjecture 00000000030: squares of {a < N : 3 ∤ a} are all 1 mod 3, so they miss 3ℕ − 3ℕ and are not intersective

The conjecture claims there is an absolute c > 0 such that, whenever A ⊆ [N] has |A| ≥ N^(1/2−c), the set {a² : a ∈ A} is intersective.

**Counterexample.** For any c > 0 and any N ≥ 3, take A_N = {a < N : 3 ∤ a}. It lies in both {1,…,N} and {0,…,N−1}, and |A_N| ≥ √N ≥ N^(1/2−c). Every a² with 3 ∤ a is ≡ 1 (mod 3). Now take E = 3ℕ, which has natural density 1/3; then E − E ⊆ 3ℤ. So neither E nor E − E meets {a² : a ∈ A_N}. The smallest case is N = 3, A = {1, 2}.

**Notions refuted.** The counterexample works under four notions of "intersective":
- the standard Sárközy–Furstenberg notion, R ∩ (E − E) ≠ ∅ for every E of positive upper density (Bienvenu–Griesmer–Le–Lê, Def. 1.1);
- the same notion with natural density;
- the statement's literal parenthetical, R ∩ E ≠ ∅ for every E of positive upper density;
- the same parenthetical with natural density.

**Other readings.** The same obstruction refutes the finitary reading (B_M = 3ℕ ∩ [M]) and the reading where A is infinite. Separately, no finite set of positive integers is intersective in these infinitary senses. This says nothing about an existential claim on an infinite square set or a finitary sparsification statement. The conjecture as written is universal ("whenever"), and that is the reading refuted.

**Lean.** Everything is proved in Lean 4 with Mathlib, including the density of mℕ (as a `Tendsto` and a `limsup`), the size bound with real powers, and the mod-3 argument. The main theorem `C30.conjecture_false` refutes all eight combinations: the four notions above under each of the two conventions for [N]. Only the axioms propext, Classical.choice and Quot.sound are used, and the build is clean with warnings treated as errors.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture30/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000030.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C30.conjecture_false`, `C30.main_family`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000000030 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
