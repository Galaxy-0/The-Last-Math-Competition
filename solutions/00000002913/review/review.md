# Solution Review — Conjecture 00000002913 (PR 693)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005122616`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual; the English text is garbled, the Chinese text carries the content). The submission's `conjecture.md` is byte-identical to `conjectures/00000002913.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization (only 2 stray characters of extraction noise); no content differences.
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `Tlmc2913.conjecture_00000002913_false` and `Tlmc2913.keller_counterexample_every_degree` depend only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` (2 lines, both clean) and `build.txt` reproduce my runs; `SHA256SUMS.txt` has stale entries for `conjecture.md`, `Basic.lean`, and `proof.tex` (actual files verified: the conjecture copy matches the official hash, the Lean file builds and audits clean, the PDF matches the shipped one).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000002913/Jackmeson1_submission_20261005122616/`; no existing solution on `main`.

## Semantic audit

The conjecture's substantive content (from the clearer Chinese text) is the finite-field-Jacobian-style threshold claim: a degree-`d` polynomial map over `F_q` is injective when `q > d²`. The submission refutes this clause under three readings, all faithful: (R1) arbitrary polynomial maps `F_q² → F_q²` of degree `d`; (R2) Keller maps (Jacobian determinant a nonzero constant — the hypothesis the definition's "jacobian conjecture" phrase names); (R3) one-variable polynomial maps. The universal reading is the only nontrivial one, and it is the one refuted; the report explicitly declines the trivial existential reading and lists further unrefuted readings (prime fields under (R2), separability-restricted variants, `d = 1`).

The witness `f_{p,m}(x,y) = (x^p − x + y^m, y)` is exactly right. Non-injectivity holds over every field: `(0,0)` and `(1,0)` both map to `(0,0)` since `1^p − 1 = 0`. Over characteristic `p` the Jacobian determinant is `p x^{p−1} − 1 = −1`, a nonzero constant, so the witness is a Keller map — refuting even the Jacobian-hypothesis reading. The degree computation `max(p, m)` is proved honestly in Mathlib's `totalDegree` (coefficient-support argument, including the degenerate `p = 1` exclusion). Over `GaloisField 2 k` with `2^k > d²` (`keller_counterexample_every_degree`, taking `m = d ≥ 2`), all stated hypotheses — degree exactly `d`, `q > d²` — are met, and `plain_counterexample` additionally covers every finite field including prime fields under (R1), and the one-variable reading `x ↦ x^d − x` (with `(x^p − x)' = −1` in characteristic `p`) under (R3).

I verified the mathematics independently: this is the classical Artin–Schreier obstruction to the Jacobian conjecture in positive characteristic, and no finite-field threshold `q > d²` can force injectivity of all degree-`d` maps since the failure `(1,0) = (0,0)` is field-independent. Refuting the first conjunct of a conjunction refutes the conjecture; the uninterpreted second conjunct ("failure ... does not exceed d by Chebyshev–Lagrange inversion") is acknowledged as uninterpreted rather than quietly assumed. The quantifier structure of the refuted clause matches the conjecture.

## Issues found

- Minor hygiene: three stale entries in `verification/SHA256SUMS.txt` (files verified correct as described above).
- The English conjecture text is garbled; the report quotes it verbatim, translates responsibly, and documents which readings are and are not refuted. No objection.

## Verdict

APPROVED. A faithful and decisive disproof of the injectivity-threshold clause, with genuine Mathlib finite fields, polynomial maps, degrees and Jacobians (in contrast to earlier numeric-placeholder attempts at this conjecture), clean build and axioms, and an unusually transparent scope statement.
