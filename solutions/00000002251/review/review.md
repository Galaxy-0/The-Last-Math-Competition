# Solution Review — Conjecture 00000002251 (PR 685)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005113208`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000002251.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization; only glyph extraction artifacts.
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `Tlmc2251.rank_ker_diffOp_gt_one` and `Tlmc2251.conjecture_2251_refuted` depend only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` and `build.txt` reproduce my runs; `SHA256SUMS.txt` has stale `conjecture.md` and `Basic.lean` entries (files verified correct).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000002251/Jackmeson1_submission_20261005113208/`; no existing solution on `main`.

## Semantic audit

The space is the one the conjecture itself names: "the spectrum of Δ_c on meromorphic function spaces". The submission makes `Δ_c` an honest `Module.End` of the submodule of meromorphic functions of `ℂ → ℂ` (Mathlib's `Meromorphic`), with closure under translate-and-subtract proved from Mathlib lemmas. Dimension is `Module.rank`, spectrum is the algebraic spectrum in the endomorphism algebra — both faithful.

Kernel clause: for `c ≠ 0` the witnesses `1` and `e^{2πiz/c}` both lie in `ker Δ_c` (`Δ_c e_b = (e^{bc} − 1)e_b`, and `e^{2πi} = 1`); independence is certified by evaluation at `0` and `c/2` (where the exponential takes values `1` and `−1`), giving `s = s′, t = t′`. For `c = 0`, `Δ_₀ = 0` and `1, z` witness. Hence `1 < rank(ker Δ_c)` for **every** `c` — the clause "the kernel of Δ_c has dimension 1" is false in the strongest possible form (in fact the kernel is the whole space of `c`-periodic meromorphic functions, infinite-dimensional). The report's remark that the same witnesses lie in the kernel on entire functions and any exponential-type subclass is correct (`|e^{bz}| ≤ e^{|b||z|}` is proved), so restricted-but-natural readings also fail; the report explicitly does *not* claim readings whose spaces exclude nonconstant periodic functions (polynomials, rationals, trigonometric polynomials with irrational `c/2π` — where the `{2 sin(kc/2)}` heuristic would live).

Spectrum clause: every `μ ≠ −1` is an eigenvalue with eigenvector `e_b`, `b = log(1+μ)/c` (so `e^{bc} = 1 + μ`); `−1` is absent because `(−1 − Δ_c)f = −f(·+c)` is a bijection with inverse `g ↦ −g(·−c)`; hence `σ(Δ_c) = ℂ ∖ {−1}`, uncountable (ℂ minus a point is not countable, proved via `not_countable_complex` and codiscrete decomposition), so it is not `{2 sin(kc/2) : k ∈ ℤ}` nor any countable-index image. I verified both directions independently: the eigenvector computation is the elementary `Δ_c e^{bz} = e^{bz}(e^{bc} − 1)`, and the shift-bijectivity of `−f(·+c)` on meromorphic functions is immediate. The Mathlib convention that a meromorphic function is an honest `ℂ → ℂ` function (values at poles) is addressed by `indep_mod_codiscrete`: the witness pair remains independent even after identifying functions agreeing off a discrete set. Refuting the kernel clause refutes the conjunction; the spectrum computation removes any fallback.

## Issues found

- Minor hygiene: two stale entries in `verification/SHA256SUMS.txt`; actual files verified.
- No mathematical or semantic issues; the readings section is notably careful about what is not refuted.

## Verdict

APPROVED. A complete and faithful disproof — kernel rank > 1 for all `c`, exact spectrum `ℂ ∖ {−1}` for `c ≠ 0` — with genuine operator theory in Lean, clean build and axioms, and a report that both corrects the earlier retracted attempt and delimits its own scope precisely.
