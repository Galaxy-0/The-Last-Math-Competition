# Disprove conjecture 00000008228: the Ehrhart function of a rank-one Weyl-orbit polytope is 2ct+1, never monic

- **Claim refuted.** The conjecture is a conjunction of four laws about the weight polytope conv(W·λ). This refutes the fourth (semisimple rank law): the Ehrhart function is a monic polynomial of degree the semisimple rank. The conjunction is therefore false.
- **Objects from Mathlib.** Rank-one `RootDatum`s on ℤ (roots ±a, coroots ±b, ab = 2; SL2 and PGL2), the Weyl group `RootPairing.weylGroup`, the polytope as the real convex hull of the Weyl orbit (proved = [−|λ|, |λ|]), and the semisimple rank as the rank of the root lattice (proved = 1).
- **Ehrhart count.** In the weight lattice, #(tP ∩ ℤ) = 2|λ|t + 1 (`ehrhart_top`); for any lattice Λ containing λ ≠ 0 the count is 2ct + 1 with c ≥ 1 (`ehrhart_formula`), so no polynomial agreeing with it at all positive integers is monic. A root-lattice version is included.
- **Lattice conventions.** For λ = the root α, every convention (weight lattice, root lattice, the coset tλ + ℤΦ) gives a non-monic count; for λ a fundamental weight the coset count is t + 1, so the coset reading is covered only for λ in the root lattice.
- **Scope.** Rank one; λ ≠ 0; clauses 1–3 are not used (clause 2 also fails: length 2n vs (n+1)/2, remarked informally).
- **Main theorems.** `C8228.semisimple_rank_law_fails`, `C8228.ehrhart_not_monic`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 268 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8228/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008228.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C8228.semisimple_rank_law_fails`, `C8228.ehrhart_not_monic`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000008228 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
