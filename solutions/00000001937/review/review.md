# Solution Review — Conjecture 00000001937 (PR 704)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005130809`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read; copy check.** Read `conjectures/00000001937.md` in full (bilingual). Shipped `conjecture.md` is byte-identical to it (`diff` clean).
- **LaTeX rebuild + PDF comparison.** Fresh `latexmk -pdf` build: exit 0, 3 pages matching the shipped PDF. Extraction differences are only glyph/font-substitution artifacts in math mode (e.g. ≅, Σ mapping differently); rendered pages are content-identical. Cosmetic.
- **Lean build.** `lake build` from scratch: zero errors, 8708 jobs, exit 0 (toolchain `leanprover/lean4:v4.33.1`, Mathlib v4.33.1, pool rev 0df444a360). Incremental rebuild of the extracted tree confirms shipped sources match the built state.
- **Axioms.** No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. Independent scratch check beyond the shipped `axioms.txt`: `conjecture_1937_false`, `subgroupCount_U`, `subgroupZetaAbscissa_U`, `subgroupZetaAbscissaAbs_U` — all `[propext, Classical.choice, Quot.sound]`, only the standard three.
- **Aux code.** `Axioms.lean` reproduces `verification/axioms.txt`. Note: `verification/SHA256SUMS.txt` has two stale entries (`conjecture.md`, `lean/Conjecture1937/Basic.lean`) that do not match the shipped files; both verified correct independently.
- **Metadata.** `metadata.csv` lists 00000001937 as unsolved (proven = false, disproven = false); no competing solution folder on main.

## Semantic audit

The conjecture defines the subgroup growth zeta function as the Dirichlet series ζ_G(s) = Σ a_n(G) n^(−s) of subgroup-index counts, and claims its abscissa of convergence equals dim G/(dim G + 1) for arithmetic linear groups, "uniquely determined by the algebraic dimension". The submission exhibits one arithmetic linear group for which the abscissa is 1 regardless of d, refuting the universally quantified formula (the "uniquely determined" clause is part of the same conjunction and falls with it).

The formalization uses the conjecture's own objects throughout. The group is not a toy surrogate: U(ℤ) is built as the range of n ↦ [[1,n],[0,1]] inside Mathlib's `SpecialLinearGroup (Fin 2) ℤ`, with `mem_U_iff` showing it is exactly GL₂(ℤ) ∩ U₂(ℚ) — the integer points of the one-dimensional unipotent algebraic group U₂ ≅ 𝔾_a — which is arithmetic under the standard definition (quoted in the report from Wikipedia and consistent with the literature). The counts a_n(G) use `Subgroup.index` and `Nat.card`; the zeta function is a Mathlib `LSeries`; and both abscissae are formalized: Mathlib's `abscissaOfAbsConv` and the infimum of real σ where the ordered partial sums converge. Because the abscissa 1 is proved different from d/(d+1) for every natural d (`formula_ne_one`), the refutation is independent of how the ambient algebraic dimension is computed; the file does not formalize "dim", and says so.

The mathematics is correct and elementary. U(ℤ) ≅ ℤ, whose subgroups are exactly nℤ with [ℤ : nℤ] = n, so a_n = 1 for every n (including the trivial-subgroup/index-0 convention, harmlessly, since the LSeries starts at n = 1); the coefficient sequence is constant 1, so ζ_{U(ℤ)} = riemannZeta on Re s > 1, whose abscissa of convergence — absolute or ordinary, read at real points — is 1 (convergence for σ > 1 via `Real.summable_one_div_nat_rpow`, divergence at σ = 1, the harmonic series). Since d/(d+1) < 1 for every natural d, the formula fails; for dim U₂ = 1 it predicts 1/2 instead of 1. I verified the classical facts invoked (unique subgroup of each index in ℤ, abscissa of ζ) independently.

The decisive content is a conjunction packaging the complete witness (the group, the counts, the identification with riemannZeta, both abscissae, and their distance from every predicted value), which is the correct way to exhibit a counterexample when the informal "arithmetic linear group" predicate is not part of the formal statement — and which cures the defect of the earlier closed PR #264, where nothing about Dirichlet series or subgroup zeta functions appeared in Lean. The report honestly delimits what is not covered (a reading restricting "arithmetic group" to arithmetic subgroups of semisimple groups; conditional convergence at non-real points); under the definition the conjecture as written states, the refutation is complete.

## Issues found

- Non-blocking: `verification/SHA256SUMS.txt` lists two hashes that do not match the shipped `conjecture.md` and `lean/Conjecture1937/Basic.lean` (stale checksums; both files verified correct independently). The other 12 entries check out.

## Verdict

APPROVED. The submission refutes the conjecture with a genuine arithmetic linear group on the conjecture's own objects — real subgroup-index counts, a real Dirichlet series, both real abscissae — proving the abscissa is 1 while the formula predicts d/(d+1) < 1 for every possible dimension; the argument is correct, dimension-convention independent, formalized with zero build errors and only the standard three axioms, and its scope limitations are accurately disclosed.
