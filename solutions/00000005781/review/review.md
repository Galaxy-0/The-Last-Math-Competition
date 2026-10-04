# Solution Review — Conjecture 00000005781 (PR 377)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004024637`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — canonical divergence's triangle deficit is an explicit Pythagorean/second-order-interaction remainder and is nonnegative (both EN and 中文 assert nonnegativity, no orthogonality/projection/ordering hypothesis).
- LaTeX: compiled fresh in /tmp/tlmc-review5/scratch/pr-377 with pdflatex twice, exit 0 both passes, 0 errors, 2 pages; shipped report.pdf is a genuine PDF (PDF 1.5) whose extracted text is identical to the recompiled output.
- Lean build: exit 0 (fresh `rm -rf .lake` rebuild; Mathlib pinned c44e0c8e…; toolchain v4.19.0 auto-present). No build warnings on Main.lean. Note: the environment's bundled v4.19.0 linker produced dyld-incompatible binaries (macOS 26 refuses leanc-linked exes), so `lake exe cache` had to be relinked with the system clang; this is a machine issue, not a submission defect. `lake build` itself (library oleans, no exe linking) needed no workaround.
- Forbidden content: none — no sorry/admit/native_decide/axiom decls/unsafe/implemented_by/extern/skipKernelTC in Main.lean; #print axioms output lists only [propext, Classical.choice, Quot.sound].
- Auxiliary code: none shipped and none required (statement is pure real analysis); my independent sympy re-derivation confirms D(x,y)=(x−y)²/2, Δ(x,y,z)=(y−x)(y−z), Δ(0,1,2)=−1, −Δ(0,2,1)=−2.
## Semantic audit
Conjecture (literal): "The triangle deficit formula is explicit as the Pythagorean remainder of dual points, the remainder being the second-order interaction of potential differences, and nonnegative." The submission takes the canonical dually flat structure on ℝ with ψ(x)=x²/2 (Hessian metric 1, zero connection coefficients, self-dual coordinates η=ψ′(x)=x) — a genuine instance of the conjecture's setting — and the canonical divergence defined by the standard potential formula. Lean signatures:
- `noncomputable def canonicalDivergence (x y : ℝ) : ℝ := potential x + potential (deriv potential y) - x * deriv potential y` — the Amari canonical divergence D(θ,η′)=ψ(θ)+φ(η′)−θη′ of a dually flat (Hessian) structure.
- `theorem canonical_is_bregman (x y : ℝ) : canonicalDivergence x y = bregmanDivergence x y` and `theorem divergence_formula : canonicalDivergence x y = (x-y)^2/2` — equivalence with the Bregman divergence, exactly as the theory requires.
- `noncomputable def triangleDeficit (x y z : ℝ) : ℝ := canonicalDivergence x y + canonicalDivergence y z - canonicalDivergence x z`, with `theorem three_point_identity (x y z : ℝ) : triangleDeficit x y z = (y - x) * (y - z)` — this IS the second-order interaction remainder (mixed second difference of the quadratic potential).
- `theorem conjecture_5781_false : ¬ (∀ x y z : ℝ, 0 ≤ triangleDeficit x y z)` and `theorem opposite_sign_also_false : ¬ (∀ x y z : ℝ, 0 ≤ -triangleDeficit x y z)` — nonnegativity fails in EITHER sign convention (witnesses (0,1,2) and (0,2,1) with distinct points), so the disproof is robust to how "Pythagorean remainder" is signed.
Supporting lemmas prove the actual derivative (HasDerivAt), Hessian = 1, strict convexity via an explicit Jensen gap, and the Legendre supremum formula — the objects named in the conjecture's definition clause are genuinely present, not numeric stand-ins (contrast with rejected PRs #286–288). The one non-formalized step is the prose identification "zero connection coefficients ⇒ dually flat" for the constant metric — a definitional/textbook fact for the Hessian structure, honestly disclosed in report and README.
## Issues found
- minor, non-blocking: "dually flat structure" itself is not formalized as a manifold-level object; flatness is argued in the report prose only (the formal model carries the potential, Legendre duality, canonical/Bregman divergence, which determine the structure uniquely here).
- minor, non-blocking: counterexample is the 1-dimensional self-dual Euclidean line — a degenerate instance, but the conjecture text carries no dimension/nondegeneracy restriction and both signs are refuted with distinct points.
## Verdict rationale
The Lean project proves, from the genuine canonical divergence of a genuine (indeed the simplest) dually flat structure, that the three-point Pythagorean/interaction remainder takes both signs, contradicting the literal bilingual nonnegativity claim under either sign convention. All definitions faithfully encode the conjecture's objects; build, PDF, and forbidden-content checks pass; no auxiliary code is needed. Approve.

## Disposition
APPROVED — merged into main (PR 377). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
