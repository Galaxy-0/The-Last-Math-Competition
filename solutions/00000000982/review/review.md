# Solution Review — Conjecture 00000000982 (PR 691)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005121556`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000000982.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization; only extraction artifacts (the largest char-multiset delta of the batch, 80 chars, all from math-font glyph mapping — no content difference; every character of the rebuild appears in the shipped text).
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `C982.conjecture_982_false` depends only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` and `build.txt` reproduce my runs; `SHA256SUMS.txt` has a stale `conjecture.md` entry (actual file matches the official conjecture).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000000982/Jackmeson1_submission_20261005121556/`; no existing solution on `main`.

## Semantic audit

The submission builds the genuine objects: Fock space membership (entire + Gaussian-square-integrable), the normalized reproducing kernel `k_z(w) = e^{w z̄ − |z|²/2}`, and the Berezin transform as an honest Bochner integral `∫ f(w)|k_z(w)|² dλ(w)` against the Gaussian probability density `π^{−1}e^{−|w|²}`. This matches the classical one-variable Fock-space Berezin transform quoted in the report (with the Wikipedia cross-check to the Segal–Bargmann kernel).

The mathematical core is correct and cleanly done. The kernel identity `|k_z(w)|² e^{−|w|²} = e^{−|w−z|²}` turns the transform into the Gaussian convolution `Bf(z) = ∫ f(z+u) G(u) du`; `∫ G = 1` gives `B(c) = c`; and the rotation argument (`∫ u^j G(u) du = 0` for `j ≥ 1`, via the measure-preserving rotation by `e^{iπ/j}` under which `u ↦ u^j G` picks up the factor `ω^j = −1`) kills every binomial term except `z^k`, so `B(w^k) = w^k` for all `k`. Every witness integral is proved integrable (`|u|^k e^{−|u|²} ≤ k! e^{1/2} e^{−|u|²/2}`), so Mathlib's integral-of-zero-for-non-integrable convention is never load-bearing — and the report addresses this convention explicitly. Consequences: `w ↦ w ∈ F²` is a fixed point (its `|w|²e^{−|w|²}` moment is integrable) and is not radial since `|1| = |i|` but `1 ≠ i`; the fixed-point set contains all constants, hence is infinite even among bounded symbols; and the monomials are linearly independent, so clause (B) fails even under a dimension reading of "cardinality ≤ 2".

The two clauses of the conjecture (radiality, cardinality ≤ 2) are a conjunction, and both fail under the Fock-space reading; under the bounded-symbol reading (R2) radiality is in fact true in the literature (bounded fixed points are constant, as the report's literature check documents), but the cardinality clause still fails, so the conjecture is false under either reading. This is consistent with the known theory — the Gaussian convolution is `e^{Δ/4}`-type and fixes all harmonic functions, so non-radial fixed points must exist. The quantifier structure ("fixed points ... are radial, and the fixed-point set is at most 2") is faithfully negated.

## Issues found

- Minor hygiene: one stale `conjecture.md` hash in `verification/SHA256SUMS.txt`; the file itself is correct.
- The report's literature section correctly anticipates that bounded fixed points are constants, i.e., clause (A) survives under (R2); the submission never overclaims this and refutes the conjunction through clause (B). No issues.

## Verdict

APPROVED. A rigorous, object-level disproof with real Fock-space machinery in Lean (Gaussian integrals, moments, kernel identities), clean build and axioms, and a report that matches the formalization point for point.
