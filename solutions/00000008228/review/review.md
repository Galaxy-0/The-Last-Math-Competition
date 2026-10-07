# Solution Review — Conjecture 00000008228 (PR 730)

**Submission:** Jackmeson1 — `solutions/00000008228/Jackmeson1_submission_20261005171148`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000008228.md` read in full (English + Chinese). Shipped `conjecture.md` is **byte-identical** to the official file.
- LaTeX: full `proof.tex` (186 lines) read. Independently rebuilt with `latexmk -pdf` in a scratch dir — succeeds (3 pages). Shipped vs rebuilt text compared with pypdf after normalization: ≥ 99.3% character-stream similarity; differences are exclusively math-glyph extraction artifacts (|·|, ⟨·,·⟩, GL₂ subscripts), no content difference.
- Lean build: `lake build` re-run — **Build completed successfully (8708 jobs), zero errors**. Lean 4.33.1, Mathlib v4.33.1 (pool rev 0df444a360).
- Axioms: fresh `lake env lean Check.lean` audit of every decisive theorem (`ehrhart_not_monic`, `semisimple_rank_law_fails`, `semisimple_rank_law_fails_rootLattice`, `ehrhart_top`, `ehrhart_formula`, `semisimpleRank_rk1`, `not_monic_of_linear`, `weightPolytope_eq`) reports exactly `[propext, Classical.choice, Quot.sound]` in all cases. Cheating grep clean (prose hits only).
- Aux code: `verification/build.txt` and `axioms.txt` match fresh reproduction; `SHA256SUMS.txt` verifies for all files except `conjecture.md` and `lean/Conjecture8228/Basic.lean`, whose recorded digests match their CRLF (pre-normalization) variants exactly — content verified intact against the PR ref and official conjecture. Non-blocking.
- Metadata: `metadata.csv` lists 00000008228 as `proven=false, disproven=false`; no solution folder on the main branch; README eligibility statement consistent.

## Semantic audit

The conjecture is a conjunction of four laws about the Satake weight polytope: (1) sat_vertex = MV-cycle weights, (2) volume = dimension/|W| normalization, (3) vertex count = extremal elements of the saturated set, (4) the Ehrhart function of the polytope is a monic polynomial of degree the semisimple rank. The submission refutes clause (4), which falsifies the conjunction.

The formalization uses the conjecture's own objects. The weight polytope under geometric Satake of the representation with highest weight λ is, by its standard definition, the convex hull conv(W·λ) of the Weyl orbit — its vertices are the extremal weights (the sat_vertex of the conjecture's definition). No formalization of the affine Grassmannian or the Satake equivalence is needed to instantiate this polytope, and using it is faithful rather than a toy surrogate: the Lean builds genuine Mathlib `RootDatum`s — for X = ℤ, roots ±a and coroots ±b with ab = 2, which are exactly the root data of SL₂ (a=2, b=1) and PGL₂ (a=1, b=2), thereby covering both readings of "the cocharacter lattice of G is the character lattice of the dual group" — with Mathlib's actual Weyl group `RootPairing.weylGroup`, the actual real convex hull (`convexHull ℝ` of the orbit, proved equal to [−|λ|,|λ|]), and an actual lattice-point count in actual dilates tQ. The semisimple rank is defined as the rank of the root lattice and proved equal to 1.

The mathematics is elementary and airtight. In rank one every reflection acts as x ↦ −x (`weyl_smul`, `orbit_eq`), so W·λ = {λ,−λ} and P_λ = [−|λ|,|λ|]; dilating gives tP_λ = [−t|λ|,t|λ|], and counting in any lattice Λ = dℤ containing λ = dm gives L_Λ(P_λ,t) = 2|m|t + 1 (`count`, `ehrhart_formula`). A function that agrees with 2ct+1 (c ≥ 1) at all positive integers equals the polynomial (2c)X + 1 by uniqueness on an infinite set, so no monic real polynomial of any degree — in particular none of degree semisimpleRank = 1 — represents the Ehrhart function (`not_monic_of_linear`, `ehrhart_not_monic`, `semisimple_rank_law_fails`). Numeric sanity: for SL₂ with λ = 1 the counts are L(1),L(2),L(3) = 3,5,7 — leading coefficient 2, not monic; this is the true state of affairs (an Ehrhart polynomial is monic iff the normalized volume is 1, which fails here), so the conjectured law is genuinely false and the counterexample is real.

The paper's handling of reading ambiguities is exemplary: since the text fixes neither the group, the weight, nor the counting lattice, it proves the failure for every nonzero λ and every lattice Λ ∋ λ (including the weight lattice, the root lattice when λ ∈ ℤΦ, and the root-lattice coset reading tλ + ℤΦ for λ ∈ ℤΦ, e.g. λ = the root α). It explicitly flags the one reading not covered — the coset count for λ a fundamental weight (which would give t+1, monic) — and notes that the law is still refuted under that reading by λ = α. The informal remark that clause (2) also fails (vol P_n = 2n vs (n+1)/2, ratio not constant) is correct, clearly labeled as outside the formal disproof, and not load-bearing. Clauses (1) and (3) are untouched — unnecessary, since refuting one conjunct refutes the whole.

## Issues found

None blocking. (Same cosmetic SHA256SUMS CRLF note as recorded in VERDICT.json.)

## Verdict

APPROVED. A faithful, complete, machine-checked disproof of the semisimple rank law on genuine SL₂/PGL₂ root data, robust under every lattice and duality convention the under-specified text admits, with zero build errors and only the standard three axioms. The conjunction of the four laws is false; the submission proves exactly its negation on a real instance.
