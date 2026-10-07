# Solution Review — Conjecture 00000000238 (PR 738)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005193021`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000000238.md` read in full (English + Chinese). Shipped `conjecture.md` is byte-identical to it (`diff` clean).
- LaTeX: full `proof.tex` read; `latexmk -pdf -interaction=nonstopmode` rebuild in a scratch dir succeeds (exit 0). pypdf text comparison of shipped vs rebuilt PDF matches after normalizing extraction artifacts only (∑/∏/∪ glyph mapping, `\texttt` underscores, ligatures, spacing); no content discrepancy.
- Lean: clean `lake build` succeeds with zero errors and zero warnings (Lean v4.33.1, Mathlib v4.33.1, 8708 jobs).
- Axioms: independent `lake env lean Check.lean` on `conjecture_238_false`, `exists_packing_denser_than_D7`, `not_D7_densest`, `similar_D7_density_lt`, `LatticePacking.filled_fraction` — all report only `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, `extern`, `unsafe`, `implemented_by`, or declared `axiom` anywhere (`lean/Axioms.lean` contains only `#print axioms` commands).
- Aux code: `verification/axioms.txt` matches the independent axiom run; `verification/build.txt` consistent with a successful fresh build. Note: `verification/SHA256SUMS.txt` has stale entries (`conjecture.md`, `lean/Conjecture238/Basic.lean`) — both files verified directly (byte-identical official copy; clean rebuild), packaging hygiene only.
- Metadata: `metadata.csv` at the PR base commit lists `00000000238` as unsolved; the PR adds only the solution folder.

## Semantic audit

The conjecture states that the densest lattice packings of non-overlapping unit balls in dimensions five, six, and seven are given by the D lattices (with the Voronoi-cell-volume determination as a methodological rider). The submission refutes the dimension-7 clause, which suffices for the negation of the conjunction, and proves the strongest natural form of it: there exists a lattice packing of unit balls in ℝ⁷ strictly denser than every lattice packing whose centers form a similar copy of D₇ (`exists_packing_denser_than_D7`), so no maximizer is of D₇ type.

The formalization is faithful. A `LatticePacking` is a discrete, full-rank ℤ-submodule whose distinct points are at distance ≥ 2 (Mathlib's `disjoint_ball_ball_iff` links this to disjoint open unit balls) — the standard definition. Density is vol(B(0,1))/covolume, and `filled_fraction` proves this equals the fraction of any fundamental domain filled by the union of balls, connecting it to the conjecture's "supremal fraction of space filled" definition. D₇ is the genuine root lattice (proved equal to the ℤ-span of eⱼ+e₇, j ≤ 6, and 2e₇, det 2), and "given by the D lattice" is correctly modeled as similarity (nonzero scale composed with a linear isometry) — covering rotations, reflections, and rescalings. No deep theorem is assumed: the code-weight bound, the determinant computations, and the covolume scaling |det φ| = 1 for isometries are all proved.

The mathematics is correct and is the classical E₇-beats-D₇ fact. The witness is the ℤ-span of the rows of A_L (the three generators of the binary [7,3,4] simplex code, plus 2e₄..2e₇), a sublattice of the Construction-A lattice E = {x ∈ ℤ⁷ : x mod 2 ∈ C}: every nonzero vector of E has squared length ≥ 4 (if x mod 2 = 0 some coordinate is a nonzero even integer; otherwise a nonzero codeword has weight 4, so four coordinates are odd), and det A_L = 16, giving density vol/16. For any similar copy of D₇, the vector c·φ(e₁+e₇) of length |c|√2 lies in the lattice, so non-overlap forces |c| ≥ √2 and covolume 2|c|⁷ ≥ 16√2 > 16 — strictly smaller density. I verified independently: all seven nonzero codewords of the simplex code have weight 4; the minimum of |x|² over E (brute force over a box) is 4; det A_L = 16, det A_D = 2; and the resulting density π³/105 ≈ 0.2953 coincides with the known E₇ lattice-packing density, with D₇ copies worse by exactly the factor √2. The unused identifications (Λ₀ = E, E = √2·E₇) are honestly disclosed as remarks.

## Issues found

None blocking. (Minor, non-blocking: stale SHA-256 entries in `verification/SHA256SUMS.txt` for `conjecture.md` and `lean/Conjecture238/Basic.lean`; both verified directly.)

## Verdict

APPROVED. The submission disproves the dimension-7 clause of the conjecture with an explicit, fully formalized lattice packing (the Construction-A/E₇-type lattice) that is provably strictly denser than every similar copy of D₇, using faithful definitions of lattice packing, density, and D-lattice similarity; the build is clean, the axiom audit shows only the three standard axioms, and the report matches the formal development.
