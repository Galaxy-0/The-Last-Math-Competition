# Solution Review — Conjecture 00000001101 (PR 371)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004020741`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "For every root system there exist x, w such that the leading coefficient of P_{x,w}(q) contains an odd prime factor beyond powers of two" (CN: 对每个根系).
- LaTeX: report.tex read in full; recompiled twice with pdflatex (exit 0); shipped report.pdf is a real PDF matching the tex.
- Lean build: fresh `rm -rf .lake && lake build`, Lean 4.19.0, exit 0, no warnings.
- Forbidden content: none — no sorry/admit/native_decide/axiom declarations/unsafe/implemented_by/extern; `#print axioms` shows only [propext, Quot.sound] for all final theorems.
- Auxiliary code: verify.py exit 0 — exact sparse Laurent-polynomial computation of the bar operation on the Hecke algebra (bar(T_s) = v⁻²T_s + v⁻² − 1), bar-invariance of C'_s = v⁻¹(1+T_s), and all four table entries with the degree bound and zero-polynomial exclusion.

## Semantic audit
The conjecture's universal quantifier ranges over every root system; A₁ = {±1} ⊂ ℝ is a reduced, irreducible, crystallographic root system (the report verifies the axioms: spanning, reflection stability s(t) = −t, Cartan integers ±2). Its Weyl group is W = {e, s} with ℓ(e)=0, ℓ(s)=1, Bruhat order e < s. The three nonzero KL polynomials are forced by the standard conditions: P_{x,x}=1 (diagonal normalization); for e < s the strict degree bound 2·deg P < ℓ(s)−ℓ(e) = 1 forces deg ≤ 0, and the constant term P(0)=1 forces P_{e,s}=1; P_{s,e}=0 since s ≰ e. Every nonzero leading coefficient is 1, and no prime divides 1 — so the existential "odd prime factor" claim fails at A₁, refuting the universal statement. The report also derives the table independently from the rank-one Hecke/canonical-basis construction (C'_s = v⁻¹(T+1), bar-invariant), which the reviewer re-checked by hand.

The Lean is genuinely non-table-dependent: `KLFamily P` states the standard KL normalization/degree/zero conditions as explicit hypotheses; `KL_unique_coeff` proves these conditions uniquely determine every coefficient in rank one; `IsLeading` properly excludes the zero polynomial; `rank_one_disproof` then proves the negation of the existential claim for EVERY KLFamily, and `certified_counterexample` discharges the hypotheses for the explicit table via `table_is_KL`. The decisive objects (Weyl group, Bruhat order, polynomial family, leading coefficients, odd prime divisibility) are all formalized — not the #286–288 vacuity pattern. LaTeX matches Lean: same table, same conditions, same conclusion.

## Issues found
- Adjudication note (non-blocking, disclosed by the author): A₁ is the smallest possible root system and the conjecture's evident intent concerned higher-rank diversity of KL leading coefficients; the bilingual text carries no rank restriction, so the literal statement is refuted. Consistent with the repo's adjudication precedent (e.g. #996, #3464, #8541).

## Verdict rationale
A correct, transparently disclosed, fully formalized rank-one counterexample: the uniqueness theorem makes the conclusion independent of any hardcoded table, everything compiles fresh with only standard logical axioms, the auxiliary script independently verifies the Hecke-algebra derivation, and the final theorem negates the conjecture's existential claim for the root system A₁ as literally stated in both language versions.

## Disposition
APPROVED — merged into main (PR 371).
