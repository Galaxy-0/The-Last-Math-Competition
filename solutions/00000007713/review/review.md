# Solution Review — Conjecture 00000007713 (PR 627)

**Submission:** AlyciaBHZ — `solutions/00000007713/AlyciaBHZ_submission_20261005101836`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

| Check | Result |
|---|---|
| Official conjecture read (`conjectures/00000007713.md`, bilingual) | pass |
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

Decisive theorems are exact negations of the conjunction of the equation clause and the only-when clause, globally and on every tail, with Hyperbolic defined by the standard curvature condition 3<=p,q and 1/p+1/q<1/2; witness pairs (4,6) and (max(K,6),max(K,6)) are genuine hyperbolic tilings, not toys. IsQuadraticIrrational is defined with the standard meaning (irrational + nonzero integer quadratic). Independent sanity check by reviewer: the claimed equation also contradicts the graph-theoretic bound lambda<=q-1 for the vertex-corona count of a q-regular tiling, reinforcing that the conjecture is false; the submission does not need this.

## Issues found

None blocking. The refutation is of internal consistency and deliberately does not compute the true corona growth rate; this is stated clearly in the report.

## Verdict

**APPROVED** — disproof.

The two precise quantitative clauses of the conjecture are jointly contradictory: clause (A) forces lambda(p,q)+lambda(p,q)^{-1}=(p-2)(q-2)-2 for all hyperbolic pairs, and any real solution of x+1/x=N with integer N>=3 satisfies x^2-Nx+1=0 and is irrational (N^2-4 is never a square for N>=3), hence is a quadratic irrational; clause (B) ('only when') would then force (p-2)(q-2) in {4,5,6,10} for every hyperbolic pair, which fails already at the genuine hyperbolic pair (4,6) (S=8) and on every diagonal pair (t,t), t>=6 (S=(t-2)^2>=16). The Lean file proves the general N>=3 lemma (discriminant strictly between consecutive squares; rational-square argument via Rat casts) and refutes both the global reading and every simultaneous-tail reading (covering 'p,q both tending to infinity'), plus the no-cutoff-exists form. This is a refutation by internal inconsistency of the conjecture's own clauses for any real-valued lambda, which is legitimate: no function at all can satisfy them. Faithful, elementary, machine-checked.
