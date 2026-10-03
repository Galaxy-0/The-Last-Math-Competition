# Solution Review — Conjecture 00000008547 (PR 340)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003130000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — (a) the Young lattice of partitions is Peck; and (b) the characteristic polynomials of all geometric Peck lattices are symmetric with symmetry midpoint at half the rank; submission refutes (b) with the five-element diamond M_3.
- LaTeX: compiled ok (pdflatex twice, exit 0, zero errors); shipped main.pdf a real 2-page PDF (48 KB) matching main.tex; recompile also 2 pages.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, "Build completed successfully", `-DwarningAsError=true`; only `#print axioms` info (propext, Quot.sound, one with Classical.choice).
- Forbidden content: none found.
- Auxiliary code: verify.cjs exit 0 — full brute force over all 32 subsets; output identical to recorded auxiliary-verification.json and auxiliary-results.json (only the `checkedAt` timestamp differs, by design). My own independent brute force confirms: rank sizes [1,3,1], max antichain 3, k-family maxima k=0..4 = [0,3,4,5,5], Möbius values [1,-1,-1,-1,2], χ coefficients ascending [2,-3,1], not palindromic. Cross-check: M_3 = flats of U_{2,3} = PG(1,2) = graphic matroid of K_3, χ = (t−1)(t−2) = t²−3t+2 ✓.
## Semantic audit
Conjecture definition "Peck = rank-symmetric strictly Sperner lattice" — the submission verifies BOTH this stated definition and the standard one (rank-symmetric + unimodal + strongly Sperner), so no convention gap.

Lean: `diamond` on Fin 5 is M_3 (0 < atoms 1,2,3 < 4). `Geometric = LatticeLaws ∧ Graded ∧ Atomistic ∧ Semimodular` — the standard finite geometric lattice definition (atomistic + upper semimodular), all proved by `diamond_geometric` via decide over the genuine 5-element structure. `Peck = RankSymmetric ∧ UnimodalAt ∧ StrongSperner`; `StrongSperner` uses k-families (no chain > k) with the exact bound Σ of k largest rank sizes, attained — proved for every k, with subsets exhaustively encoded in Fin 32 and `every_prop_subset_encoded` covering arbitrary Prop-valued subsets. `StrictSperner` (source's wording) proved via `unique_maximum_antichain` (every max antichain = the middle rank layer 14). Möbius: `MobiusRecurrence` is the defining recurrence Σ_{y≤x} μ(y) = [x=bot]; `diamond_mobius_unique` proves EVERY solution equals diamondMobius, so χ is not a hand-declared polynomial: `characteristicCoefficient` sums μ over rank-fibers giving [2,-3,1] i.e. t²−3t+2. `CoefficientSymmetric` (c_i = c_{r−i}, i.e. symmetric about half the rank 1) is refuted since c_0=2 ≠ 1=c_2; alternative readings of "symmetric" (value reflection / root reflection about 1) are separately refuted (`diamond_value_reflection_fails`, `diamond_root_reflection_fails`: χ(2)=0 but χ(0)=2).

Final theorem:
`GeometricPeckSymmetryAssertion : ∀ L : LatticeData, ∀ mu, Geometric L → Peck L → StrictSperner L → MobiusRecurrence L mu → CoefficientSymmetric L mu`
`conjecture_8547_false : ¬ GeometricPeckSymmetryAssertion` — the 5-element specialization of the conjecture's universal claim, with all hypotheses proved for the diamond (so not vacuous; the Möbius hypothesis is satisfiable and uniquely pinned). Since the conjecture asserts the symmetry for ALL geometric Peck lattices, failure on the 5-element instance refutes it; the Young-lattice conjunct (true) is irrelevant to the conjunction's falsity. Report's numbers (χ=t²−3t+2, ranks (1,3,1), μ(1̂)=2) match the Lean exactly.
## Issues found
- none blocking.
## Verdict rationale
M_3 is a textbook geometric lattice (flats of U_{2,3}/PG(1,2)), Peck under both the conjecture's stated definition and the standard one, and its characteristic polynomial t²−3t+2 is not symmetric about half its rank under any reasonable reading — all verified in Lean with genuine exhaustive checks (unique Möbius solution, all 32 subsets, all k). Fresh build, auxiliary reproduction, and my independent brute force all agree. Genuine disproof.

## Disposition
APPROVED — merged into main (PR 340). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
