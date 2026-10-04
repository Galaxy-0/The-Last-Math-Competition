# Solution Review — Conjecture 00000007130 (PR 540)

**Submission:** jilint777 — `jilint777_submission_20261004162941`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Verification

Full report/PDF, Lean source, and Python source read. Fresh two-pass PDF compile, exact Python verification, full self-contained Lean build, direct warning-as-error Lean check, and rendering all exited 0. No forbidden proof shortcut occurs; principal theorems use only standard permitted axioms.

## Disproof

For the rational triangle

`T = conv{(0,0),(1,1/2),(2,0)}`,

the vertex-denominator lcm is 2. But `(x,y)∈tT∩Z²` iff `y≥0`, `2y≤x`, and `x+2y≤2t`. Row summation gives

`#(tT∩Z²)=(t+1)(t+2)/2`

for every integer `t≥0`. Hence the Ehrhart quasi-polynomial is a polynomial and has minimal period 1, not the denominator lcm 2.

The report also covers facet-denominator, coefficient-denominator, lattice-only, integer-programming, and weak-period readings. In particular `conv{(0,0),(1,0),(0,1/2)}` has facet-denominator lcm 1 but exact Ehrhart period 2, refuting even the weak facet form. The strictly lattice-vertex reading would make the first clause vacuous (`1=1`), and the report states this rather than hiding it.

Lean formalizes rational membership, facets, exact finite counts, quasi-polynomial periods and minimal periods, both counterexamples, and final claim failures. Python independently recomputes all counts and periods.

**Disposition: APPROVED.**
