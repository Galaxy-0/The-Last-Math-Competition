# Solution Review — Conjecture 00000004053 (PR 690)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005120439`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000004053.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization; only glyph extraction artifacts (49 chars, all math-font mapping; the rebuild's text is a subset of the shipped extraction).
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `C4053.conjecture_4053_false` and `C4053.trivial_module_counterexample` depend only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` and `build.txt` reproduce my runs; `SHA256SUMS.txt` has stale `conjecture.md` and `Basic.lean` entries (shipped files verified correct: the conjecture copy matches the official hash and the Lean file builds/audits clean).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000004053/Jackmeson1_submission_20261005120439/`; no existing solution on `main`.

## Semantic audit

This is a real representation-theoretic disproof, with the actual objects in Lean. The group algebra `A = F₃[C₃]` (Mathlib `MonoidAlgebra (ZMod 3) (Multiplicative (ZMod 3))`) is analyzed through `t = g − 1`: `t³ = 0`, `t² ≠ 0` (coefficient at `g` is 1 in `t² = g² + g + 1`), and `a = ε(a) + t·d` for all `a`, so `ker ε = (t)`. Projective covers are defined faithfully (projective + surjective + superfluous kernel, Mathlib/Wikipedia definition), syzygies are a *relation* (`N ≅ ker π` for some projective cover), and — importantly — the submission proves the kernel of *every* projective cover of a cyclic module `A·m₀` with `m₀ ∉ tM` is isomorphic to `ann(m₀)`, so the period does not depend on cover choices.

For the trivial module `k` (with `a·x = ε(a)x`): `Ωk ≅ ker ε = (t)`; `(t)` is again cyclic on `t` with `t ∉ t·(t)` (else `t² = 0`); so every syzygy of `Ωk` is `ann(t) = (t²)`, and `x ↦ x t²` is an `A`-isomorphism `k → (t²)` (injective since `t² ≠ 0`, surjective since `a t = 0` forces `a = ε(d′)t²`). Hence `Ω²k ≅ k`, while `Ωk ≇ k` (`t` kills `k` but `t·t = t² ≠ 0` in `(t)`), so the minimal period is exactly 2. I verified this against the standard description `F₃[C₃] ≅ F₃[t]/(t³)`: Ω¹k = rad = (t), Ω²k = (t²) ≅ k — period `p − 1 = 2` for `C_p`, as the classical theory predicts.

The formalized `Clause1` quantifies over *all* subgroups `D ≤ H` rather than only defect groups of blocks ("defect group", "admissible prime" being undefined in the text). This is a strict weakening — the refuted statement is implied by the conjecture's first clause, since every defect group is a subgroup — so the refutation is a fortiori valid, and the report says exactly this. Both readings of "prime factors of the period divide prime factors of |D|" (`q ∣ r` for some prime factor `r`, and `q ∣ |D|`) are refuted at `(p, G, n, q) = (3, C₃, 2, 2)`, using `|D| ∈ {1, 3}` by Lagrange's theorem. Refuting the first clause refutes the conjunction; the unformalized second clause ("every power of every admissible prime is realized in some explicit block") is flagged, not hidden. The hypotheses imposed on the witness module (finitely generated, indecomposable, non-projective, periodic) are natural strengthenings of "periodic module" that only strengthen the counterexample.

## Issues found

- Minor hygiene: two stale entries in `verification/SHA256SUMS.txt` (verified as above).
- The stable-module-category reading of `ΩⁿM ≅ M` and the block/defect-group structure itself are not formalized; neither is needed for the refutation direction taken. Documented in the report's scope section.

## Verdict

APPROVED. A substantive, faithful disproof with genuine group-algebra, projective-cover and syzygy machinery in Lean (in contrast to the earlier vacuous attempt at this conjecture), clean build and axioms, and a report whose scope statement is precise and honest.
