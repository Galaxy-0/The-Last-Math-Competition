# Solution Review — Conjecture 00000008236 (PR 515)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004172500`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read independently. The report correctly targets its asserted first value `4/3` for the atomic-congestion-game POA spectrum and does not silently alter the other clauses.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded. The shipped and rebuilt two-page PDFs contain the same report; apparent extraction differences are only alternate ToUnicode mappings for displayed summation/brace glyphs. No TeX warnings.
- Lean: official pinned dependencies were linked; fresh `lake build` and direct `lake env lean -DwarningAsError=true Main.lean` succeeded under Lean 4.19.0/Mathlib `c44e0c8e...`.
- Axioms: all eleven printed results depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary programs: none supplied or needed; the proof is exact.
- Base metadata marks the conjecture unsolved.

## Semantic audit
Take any nonempty finite player and resource sets and positive constant latencies `c_r`. A profile's player cost is its chosen `c_r`, and Nash equilibrium means each player already chose a globally minimum constant latency. Such an equilibrium exists by assigning everyone to a cheapest resource. At any equilibrium, each term is no larger than the corresponding term of any alternative profile, so equilibrium social cost is the global minimum. Since social cost is positive, every equilibrium ratio is exactly 1 and the POA is 1. This is true for the entire positive constant-latency class, whose tight supremum is attained at 1.

The explicit two-player/two-resource all-ones game has four Nash profiles, social cost and optimum both 2, and POA 1. All mixed distributions also have expected cost 2. These are positive nondecreasing latency functions, and the source does not exclude POA 1, constant latencies, or singleton-resource atomic congestion games. Hence 1 belongs to the asserted value spectrum before 4/3, so 4/3 cannot be its first value. One false conjunct suffices to reject the full statement.

The Lean definitions use actual loads, latency costs, unilateral deviations, Nash inequalities, social-cost infimum, ratio-set supremum, positive monotone latency admissibility, and a least-spectrum-value statement. The general constant-latency theorem and explicit instance are proved without hiding the conclusion in a definition.

## Issues found
None blocking.

## Verdict
APPROVED. The exact atomic congestion game has POA 1, the whole positive constant-latency singleton class has tight POA 1, and the independent Lean/PDF/axiom checks all pass.
