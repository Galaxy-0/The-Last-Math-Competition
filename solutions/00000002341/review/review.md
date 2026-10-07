# Solution Review — Conjecture 00000002341 (PR 686)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005113559`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000002341.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization (one-character extraction delta); no content differences.
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `C2341.conjecture_2341_false` and `C2341.areaIdentity_iff_scalar` depend only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` and `build.txt` reproduce my runs; `SHA256SUMS.txt` has stale `conjecture.md` and `Basic.lean` entries (files verified correct).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000002341/Jackmeson1_submission_20261005113559/`; no existing solution on `main`.

## Semantic audit

The formalization uses the standard conventions and says so: operator 2-norm (Mathlib `Matrix.Norms.L2Operator`), pseudospectrum `{z : ‖(A−zI)⁻¹‖ > ε⁻¹}` with the universal convention `‖(A−zI)⁻¹‖ = ∞` at eigenvalues (so the spectrum is included — the standard definition, matching Wikipedia), Lebesgue area on `ℂ`, and Frobenius/Hilbert–Schmidt norm. None of these choices is load-bearing in a way that could manufacture the refutation: the two area bounds (ε-discs around distinct spectral values inside; the `‖a‖+ε` disc outside) hold in any unital Banach algebra with `‖1‖ = 1`.

The submission's `areaIdentity_iff_scalar` is the mathematical heart and is correctly proved: if the identity `area Λ_ε(A) = πε²(1 + hs(A*A − AA*)/2)` holds for all `ε`, then (Step 1) the HS deviation must vanish — otherwise the identity's `πε²·c/2` growth beats the `π(‖A‖+ε)²` upper bound at `ε = 2(2R+R²)/c + 1` (I checked the algebra: `cε²/2 > 2Rε + R²` at that ε); so `A` is normal. (Step 2) two distinct spectral values would give `area ≥ 2πε² > πε²`, contradicting the identity with `c = 0`. (Step 3) a normal matrix with one-point spectrum `λ` has `‖A − λI‖ = spectral radius = 0` (Mathlib's `IsStarNormal.spectralRadius_eq_nnnorm`), so `A = λI`. The converse (scalar matrices: pseudospectrum is the ε-disc, area `πε²`, HS term 0) is proved via `pseudo_scalar`. Hence the identity holds only for scalar matrices, and `diag(1,−1)` — normal, conjectured area exactly `πε²`, actual area ≥ `2πε²` for `ε ≤ 1` by two disjoint discs around ±1 — refutes the identity, and with it the conjunction. The `no_exact_eps_sq_law` theorem additionally kills the "area growth is exactly ε²" clause in the `Kε²` reading (K ≥ 2π from small ε, K ≤ (4R+1)²/(3R+1)² < 2π at `ε = 3R+1`).

The "random matrix" phrase is handled honestly: the identity-as-stated (an explicit formula in `A`'s own HS deviation) is a per-matrix claim and is refuted for every non-scalar matrix; the report's readings section notes the a.s.-per-realization reading fails for any ensemble giving positive weight to non-scalar matrices, declines to formalize the expected-area reading, and explicitly does not touch the asymptotic `Θ(ε²)` reading of the growth clause. None of these caveats can rescue the conjunction, since clause (i) fails under the natural reading.

## Issues found

- Minor hygiene: two stale entries in `verification/SHA256SUMS.txt`; actual files verified.
- No mathematical or semantic issues.

## Verdict

APPROVED. An unusually strong disproof — a full characterization (identity ⟺ scalar matrix) rather than a bare counterexample — with clean Banach-algebra and C*-arguments in Lean, clean build and axioms, and a report that matches the Lean statement for statement.
