# Solution Review — Conjecture 00000008256 (PR 321)

**Submission:** feiyuceng06-prog — `feiyuceng06-prog_submission_20261003084907`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0, Mathlib v4.33.1)
- [x] No `sorry`, no `native_decide`, no extra axioms (`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`)
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
Clause 1: the size of a maximal Condorcet domain (cond_max, admitting Condorcet winners) is at most the Fishburn-type bound 2^{n-1}·n!/2^{n(n-1)/2}.

## What the submission proves
The single-peaked domain on three alternatives — the four orders in which the middle alternative is not ranked last, S = {012, 102, 120, 210} — is a maximal Condorcet domain with |S| = 4 > 3 = B(3). Black's theorem is proven for every odd number of voters (three cases: strict majority ranking 0 first; strict majority ranking 2 first; otherwise 1 beats both by the complement count), maximality by the two decided cyclic 3-voter profiles (021,210,102) and (201,012,120). Lean: `admitsCondorcetWinners_singlePeaked`, `isMaximalCondorcetDomain_singlePeaked`, `conjecture_00000008256_false : ¬ SizeBound` (plus a primed version covering any reading of the other three clauses).

## Verification notes
`lake build` exit 0; axiom audit clean (build-log `#print axioms` plus an independent `lake env lean` audit). The formalization is genuine: rankings as `Equiv.Perm (Fin n)`, strict-majority `Beats`, `AdmitsCondorcetWinners` over all odd profiles, inclusion maximality, and the bound evaluated on the actual domain at n = 3. Reviewer re-checked the cyclic profile (021, 210, 102) by hand: 0 beats 2, 2 beats 1, 1 beats 0 — a majority cycle, no Condorcet winner. The B(3) = 3 evaluation is kernel-checked. LaTeX consistent; PDF present.

## Verdict
APPROVED — merged into main.
