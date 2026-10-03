# Solution Review — Conjecture 00000002058 (PR 208)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261002084239`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Algebraic sets over M_n(K) are Noetherian iff n <= 2; concretely, algebraic sets over M_3(K) are non-Noetherian. Noetherianity is equational: every system of equations is equivalent to a finite subsystem.

## What the submission proves
eqNoetherian proves M_n(K) is equationally Noetherian for every n and field: the generic matrix (entries = commutative polynomials in the k*n^2 unknowns) turns any system into a polynomial system in finitely many variables; Hilbert's basis theorem gives a finite equivalent subsystem. Instantiating at K = Q, n = 3 refutes the iff.

## Verification notes
On the conjecture's literal objects (noncommutative equations with M_n(K) constants, solution sets); the chain solutions S0 = solutions S verified in both directions. The generic-matrix argument is the standard proof of exactly this theorem.

## Verdict
APPROVED — merged into main.

