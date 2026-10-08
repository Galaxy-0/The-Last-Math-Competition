# Solution Review — Conjecture 00000009688 (PR 831)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261007102941`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-07

## Checklist results
- Conjecture read: yes — the source asserts (i) that the number of common zeros of two algebraic-coefficient exponential polynomials is an explicit function of the intersection of their exponent sets, and (ii) that when that intersection is empty an explicit zero-separation constant (a Bézout-type inequality) exists.
- Change scope: only `solutions/00000009688/gaochengzhecpu_submission_20261007102941/` was added; the conjecture is unsolved in the base metadata.
- LaTeX: `main.tex` read in full; the argument is elementary and complete.
- Lean build: Lean 4.19.0, Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Independent fresh `lake build` exit 0. Direct `lake env lean -DwarningAsError=true Main.lean` exit 0.
- Forbidden content: none (`sorry`, `admit`, `native_decide`, axiom, `unsafe`, `implemented_by`, `extern`, `skipKernelTC`).
- Auxiliary code: `verify.py` re-run — PASS (exact integer polynomial supports and factorization).
- Axioms: standard `[propext, Classical.choice, Quot.sound]` only.

## Semantic audit
The counterexample compares two pairs with identical full exponent sets. Let `f = e^z − 1` (support `{0,1}`), `g = e^{3z} − e^{2z}` and `h = e^{3z} + e^{2z}` (both support `{2,3}`). Since `g = e^{2z}·f`, every `z_k = 2πik` with `e^{z_k} = 1` is a common zero of `f` and `g`, and these are distinct — infinitely many common zeros. Conversely `f(z) = 0` forces `e^z = 1`, hence `h(z) = 2 ≠ 0`, so `f` and `h` have no common zeros. The two pairs share the exponent sets `{0,1}` and `{2,3}`, hence the same empty intersection, yet have different common-zero counts. The Lean project formalizes this with genuine `Polynomial.support`, `Complex.exp`, and `Set.encard`, proving `no_intersection_count_formula` (no function of the exponent-set intersection can give all common-zero counts) and `no_positive_zero_separation` (no `δ > 0` separates the two zero sets). Both conjuncts of the conjecture are refuted.

## Issues found
none blocking.

## Verdict rationale
The disproof is correct, non-vacuous, and fully formalized; the Lean project compiles with only the three standard axioms and contains no forbidden content. The report and the Lean statements agree.

## Disposition
APPROVED — ready to merge (PR 831).
