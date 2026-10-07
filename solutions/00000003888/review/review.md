# Solution Review — Conjecture 00000003888 (PR 734)

**Submission:** Jackmeson1 — `solutions/00000003888/Jackmeson1_submission_20261005174500`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (bilingual, `conjectures/00000003888.md`): HK density function = limit of relative eHK as a function of x; Clause 1: for a fixed ideal it is piecewise linear with finitely many breakpoints; Clause 2 (converse): explicit one-parameter ideal families with unboundedly many breakpoints. Shipped `conjecture.md` is **byte-identical** to the official file.
- **LaTeX rebuild**: `latexmk -pdf` in a scratch dir succeeds (3 pages, same as shipped). pypdf text comparison: content matches; differences are extraction artifacts of the shipped PDF's font map (`|` → `j`-like glyphs, kerning splits such as "T rivedi"/"F robenius", missing interword spaces). Cosmetic only.
- **lake build**: fresh build succeeds with **zero errors and zero warnings** (8708 jobs, Lean v4.33.1, Mathlib v4.33.1 rev 0df444a360 from poolM05), reproducing `verification/build.txt`.
- **Axioms**: `lake env lean Axioms.lean` run fresh: `C3888.conjecture_false` depends only on `[propext, Classical.choice, Quot.sound]`, matching `verification/axioms.txt`. Cheat-grep clean (only benign doc mentions).
- **Aux code**: verification files' claims (build success, axiom output) reproduced exactly.
- **Metadata**: `metadata.csv` lists 00000003888 as unsolved; no solution folder for this ID on `main`.

## Semantic audit

The conjecture is a conjunction: (1) the HK density function of a fixed ideal is piecewise linear with finitely many breakpoints, and (2) conversely there exist explicit one-parameter ideal families whose breakpoint counts grow unboundedly. The submission attacks clause (1), which is the correct exact-negation strategy for a conjunction: refuting one conjunct refutes the whole, whatever the other means, and `C3888.conjecture_false` accordingly formalizes clause (2) as an arbitrary proposition `Clause2` while proving `¬(Clause1 ∧ Clause2)`. The formalized Clause1 is a universal statement over standard-graded polynomial rings `K[x_1,…,x_n]` over a field of characteristic p > 0 and their homogeneous ideals of finite colength — the natural scope of the definition line, which the text does not restrict by dimension; refuting it at n = 3 refutes the universal, and with it any stronger unrestricted version.

The definition is the sensitive point for faithfulness, and it is handled well: the submission quotes Trivedi's definition of the Hilbert–Kunz density function (arXiv:1510.03294 — `HKd(M,I)(x) = lim_n (1/q^{d-1})·ℓ(M/I^[q]M)_{⌊xq⌋}`, q = p^n), which is a genuine literature instantiation of the conjecture's own words ("limit of relative eHK as a function of parameter x"), and the Lean `frobeniusPower`/`gradedPiece`/`hkApprox`/`hkDensity` mirror it exactly (Frobenius powers, graded pieces, `limUnder`). This is not a toy surrogate: the witness is the canonical ideal `(x,y,z)` of `k[x,y,z]` with its standard grading, proved homogeneous and of finite colength, with `(x,y,z)^[q] = (x^q,y^q,z^q)` via the freshman's dream in characteristic p, and `dim_k (R/(x^q,y^q,z^q))_m = C(m+2,2)` for m < q (all degree-m monomials are standard), giving f_n(x) = C(⌊xq⌋+2,2)/q² → x²/2 on [0,1). I verified this numerically (q = 1024, x = 1/2 gives ≈ 0.1257 → 0.125 = x²/2). Since x²/2 is not affine on any nondegenerate interval (three-point second-difference (b−a)²/16 > 0) and any finite breakpoint set leaves an open subinterval of (0,1), the density is not piecewise linear on any domain containing (0,1) — clause (1) is false. Two robustness notes: under the alternative Han–Monsky reading of "HK density" (limit of ℓ(R/I^{⌈xq⌉})/q^d) the same ideal gives x³/6, also not piecewise linear, so the informal refutation does not hinge on the definitional choice; and the tex honestly discloses that Trivedi's piecewise-linearity theorem holds in dimension 2, while the text under review does not restrict dimension, so the dimension-3 counterexample is in scope.

The submission does not address clause (2) at all — correctly so: it need not, since clause (1) is refuted outright.

## Issues found

- `verification/SHA256SUMS.txt` is stale: its entries for `conjecture.md` and `lean/Conjecture3888/Basic.lean` are pre-final-commit hashes. Non-blocking: `conjecture.md` is byte-identical to the official file, and the build/axiom claims were re-verified fresh on the shipped source.
- The tex quotes Trivedi's Example 3.1 as retrieved context but does not use it in the Lean proof — disclosed as such. Cosmetic.
- The definitional caveat above (Trivedi graded-piece variant vs Han–Monsky truncated-power variant) is worth recording; it does not affect the verdict because both readings make clause (1) false for the exhibited ideal.

## Verdict

APPROVED. The submission identifies the correct logical target (the universal first clause of a conjunction), instantiates the conjecture's definition with the published Trivedi definition it explicitly cites, computes the genuine density function of the canonical 3-variable maximal ideal in Lean from first principles, proves it equals x²/2 on [0,1), and derives the precise non-piecewise-linearity that falsifies clause 1 and hence the conjecture. Build, axioms, source-fidelity and PDF checks all pass; the only findings are the stale checksum file and a definitional caveat that the refutation survives either way.
