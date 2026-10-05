# Solution Review — Conjecture 00000008376 (PR 555)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004195709`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read in full from `conjectures/00000008376.md` (English + Chinese). No SOURCE.md is present; the submission ships README/VERIFICATION.md describing scope. The conjecture is a four-clause conjunction (McKay graph = C_n; orbit count = k!·S(n,k); maximum stabilizer = S_{n-1}; stabilizer spectrum Young-complete).
- LaTeX report `report.tex` read in full; independently rebuilt with `latexmk -pdf` (pdflatex) — compiles cleanly; whitespace-stripped pypdf extraction of shipped (Tectonic) vs rebuilt PDF matches exactly (2536 = 2536 chars).
- Fresh `lake build` on Lean v4.19.0, Mathlib pinned at c44e0c8e (prebuilt pool linked): **Build completed successfully**, 1217 targets, zero errors, zero warnings.
- Axiom audit: 12 `#print axioms` lines — every audited theorem (including `counterexample`) depends only on `[propext, Classical.choice, Quot.sound]`.
- Grep for `sorry`, `native_decide`, `axiom` declarations, `unsafe`, `@[implemented_by]`, `extern`, `admit` across the submission: only a prose mention in VERIFICATION.md stating none are used.
- Auxiliary code: none required (no scripts); the counterexample was independently re-verified numerically in python (below).
- `metadata.csv` on main marks 00000008376 neither proven nor disproven (unsolved).

## Semantic audit
The conjecture's third clause asserts that for the S_n action in tropical symmetry, "the maximum stabilizer (the largest) is S_{n-1}" (极大/最大稳定子为 S_{n-1}, 单点稳定律). The submission disproves exactly this clause with n = 3. In the max-plus semiring, the polynomial F = X_0 ⊕ X_1 ⊕ X_2 evaluates to h(x) = max(x_0,x_1,x_2) and its tropical hypersurface is the corner locus where at least two coordinates attain the maximum. The cell where all three coordinates attain the maximum is C_{012} = {(c,c,c) : c ∈ ℝ} — a nonempty, lower-dimensional but genuine cell of the cell structure, containing o = (0,0,0). Under the coordinate permutation action, every σ fixes o, so Stab_{S_3}(o) = S_3 with 3! = 6 elements, strictly larger than |S_2| = 2, and not isomorphic to S_2 (different orders). Since neither language version excludes central cells, fixed points, or lower-dimensional cells from the stabilizer spectrum, the one-point-stabilizer law fails as stated; refuting one conjunct refutes the conjunction. I re-verified numerically in python: the origin has all 6 permutations in its stabilizer while a generic point has only the identity, and |S_2| = 2 < 6.

The formalization is faithful and uses real objects throughout: `polynomial` is an actual `MvPolynomial` over Mathlib's `Tropical (WithTop ℝᵒᵈ)`, with `actual_polynomial_evaluation` proving the untroped evaluation equals the max-height; `Corner` is the honest corner locus; `Cell S` is the exact monomial-attainment description (x_i = h(x) ↔ i ∈ S); the S_3 action is a genuine `MulAction` and stabilizers are `MulAction.stabilizer` subgroups, with `point_stabilizer_top` proving the stabilizer is ⊤ and `point_stabilizer_card` computing 6 via an explicit equivariance with `Equiv.Perm (Fin 3)`. The projective story is also genuinely constructed: a `Setoid` quotienting by diagonal translations with `height_translate` proving descent, an induced `MulAction` on the quotient via `Quotient.map`, `central_cell_projects_to_one_point` showing the central cell collapses to the single projective vertex, and `projective_stabilizer_card` giving order 6 there too. `no_stabilizer_isomorphism` rules out the escape "it is merely a differently embedded S_2". The report's mathematics matches the Lean theorems clause by clause, and the scope paragraph honestly delineates what is not claimed (McKay-graph, orbit-count, Young clauses untouched — indeed S_3 itself is a Young subgroup, so no tension with the fourth clause).

Quantifier structure is right for a disproof: the clause is a universal law over the setting; one explicit instance (n = 3, standard tropical line, central point) satisfying all stated hypotheses and violating the conclusion suffices, and that is exactly what `counterexample` packages (origin in corner locus, in central cell, stabilizer = ⊤, both cardinality inequalities).

## Issues found
None blocking.

## Verdict
APPROVED. The submission disproves the maximum-stabilizer clause of the official conjecture with an explicit, fully formalized tropical counterexample (central cell of the standard tropical line fixed pointwise by all of S_3), all mechanical checks pass (clean rebuild, matching PDF, zero-error build, standard axioms only, no forbidden constructs), and the mathematics is correct and independently re-verified.
