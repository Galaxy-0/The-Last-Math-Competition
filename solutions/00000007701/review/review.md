# Solution Review — Conjecture 00000007701 (PR 625)

**Submission:** AlyciaBHZ — `solutions/00000007701/AlyciaBHZ_submission_20261005101836`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

| Check | Result |
|---|---|
| Official conjecture read (`conjectures/00000007701.md`, bilingual) | pass |
| LaTeX report read in full; rebuilt with `latexmk -pdf` | pass |
| Shipped vs rebuilt PDF text (pypdf, glyph-normalized) | pass |
| `lake build` (Lean v4.33.0, Mathlib db584cd6d4, prebuilt pool) | pass |
| Axiom audit (`#print axioms`, scratch checks; allowed set only) | pass |
| `verify.py` executed; output matches shipped `verification.txt` | pass |
| No `sorry`/`native_decide`/`admit`/`extern`/`unsafe`/`axiom` | pass |
| Faithfulness gate (conjecture's own objects, no surrogate) | pass |
| Semantic audit (exact quantifiers/objects) | pass |

Build facts: `lake build` exits 0 with no errors; the only reported axioms are
`propext`, `Classical.choice`, `Quot.sound` for this PR every audited theorem depends only on `propext`, `Classical.choice`, `Quot.sound`; the Lean source
SHA-256 in `verification.txt` matches the shipped source; the rebuilt PDF has the
same page count as the shipped one and identical extracted text modulo
ligature/smart-quote glyph-extraction artifacts introduced by font subsetting.

## Semantic audit

Decisive theorem literal_volume_clause_false is the exact negation of the universal half-integer clause over the formal IsPhysicalBRS class (measurability, finiteness, uniform discrepancy over ALL real intervals with the true covolume normalization); literal_area_spectrum_not_discrete proves the formal nondiscreteness. The windows are the conjecture's own objects (cut-and-project windows), not toys. IsPhysicalBRS is a faithful, strong rendering of the d=1 bounded-remainder window notion; the report cites Grepstad-Lev and Haynes-Kelly-Koivusalo and proves the needed relation directly. Circle (m=1) and torus readings are retained as secondary refutations.

## Issues found

None blocking. Note: the polytopal iff clause is not addressed (not needed); the verification.txt transparently flags the human lattice-admissibility bridge; the shipped report.pdf (257820 bytes) matches the shipped text and my rebuild has identical page count (7) and text.

## Verdict

**APPROVED** — disproof.

The submission refutes the second conjunct ('for d=1, m=2 the volume spectrum of W is a discrete set with all values in (1/2)Z') at the conjecture's own literal dimensions: a rank-three cut-and-project scheme with physical R and internal R^2, lattice gamma(k,m,n)=(k+sqrt2*m+sqrt3*n, (m-sqrt2*k, n-sqrt3*k)) of covolume 1+2+3=6, and windows W_q=[0,{q*(-sqrt2)})x[0,1). The Lean proves exact model-set counting on every real half-open interval (Hecke-Ostrowski coboundary + canonical-cell reindexing + inner/outer block sandwich, with explicit local finiteness), bounded-remainder membership with constant q+2, irrationality of vol(W_q)={-q*sqrt2} for q>=1 (hence not in (1/2)Z), density of these BRS areas in (0,1), and formal nondiscreteness of the resulting area spectrum. The only human bridge - discreteness/covolume/injectivity of the physical projection/density of the internal projection of the lattice - is elementary, proved in the report (I verified the arguments: determinant 6; Q-linear independence of 1,sqrt2,sqrt3; Z^2+sqrt2 Z x sqrt3 Z density), and is neither assumed in Lean nor hidden. Refuting one conjunct refutes the conjecture.
