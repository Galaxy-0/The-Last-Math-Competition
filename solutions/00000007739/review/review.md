# Solution Review — Conjecture 00000007739 (PR 581)

**Submission:** jilint777 — `jilint777_submission_20261004191325`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read (`conjectures/00000007739.md`): the claim is that for free words `W` of length `d` in a free semicircular family, `M_p(d) = ‖W‖_p/‖W‖₂` satisfies `M₄(d)² = 2 − d⁻¹(1 − (1/2)^d)` (plus a vague clause about `M_∞(d)/M_p(d)`).
- LaTeX report independently rebuilt with `latexmk -pdf`: clean build; extracted text identical to the shipped `report.pdf` after bullet-glyph normalization (same length, no content differences).
- Lean: fresh `lake build` on `leanprover/lean4:v4.19.0`, zero errors/warnings; build log identical to the one in `verification.txt`.
- `#print axioms` (Main.lean lines 344–359): only `propext` and `Quot.sound`. No `sorry`/`native_decide`/`axiom`/`unsafe`/`implemented_by`/`extern`/`admit`.
- `verify.py` rerun: 44 PASS, 0 FAIL; output identical to `verification.txt` except the trailing wrapper `exit 0` line. It recomputes all moments exactly by two independent methods (sparse Fock-space operators and counting monochromatic non-crossing pairings), agreeing on all 9841 words of length ≤ 8 in three letters.
- Independent recomputation (reviewer's own code): enumerated non-crossing pairings myself; `τ(W*W) = 1` and `τ((W*W)²) = d+1` for `W_d = s₁⋯s_d`, `d = 1..5`, so `M₄(d)⁴ = d+1 ≠ f(d)²` for every tested `d`, and at `d = 1`, `M₄(1)⁴ = 2 ≠ 9/4 = f(1)²`.

## Semantic audit
The conjectured identity at `d = 1` reads `M₄(1)² = 3/2`. A free word of length one is a single standard semicircular element `s`; in Voiculescu's Fock-space realization `s = ℓ(e₀)+ℓ(e₀)*`, and the submission computes `‖s‖₂² = τ(s²) = 1` and `‖s‖₄⁴ = τ(s⁴) = 2` (two non-crossing pairings of four points; the Catalan number `C₂`). Hence `M₄(1)⁴ = ‖s‖₄⁴/‖s‖₂⁴ = 2`, so `M₄(1)² = √2 ≠ 3/2`. The Lean development constructs everything from scratch: basis words `List Nat`, finitely supported integer vectors, the creation operator (prefixing) and its adjoint (stripping), the semicirculars `X_i`, the vacuum state, and — crucially — proves the adjointness lemmas (`inner_create`, `inner_annih`, `X_selfadjoint`, `applyW_adjoint`) and the norm identities `norm2sq_eq`/`norm4pow4_eq` that connect `τ(W*W)` and `τ((W*W)²)` to `⟨WΩ, WΩ⟩` and `⟨W*WΩ, W*WΩ⟩`, which is exactly how `L²` and `L⁴` norms are computed in a tracial vacuum state. `semicircle_moments` verifies the Catalan moment sequence `1,0,1,0,2,0,5,0,14,0,42`, certifying that `X₀` is standard semicircular.

The clause is encoded without real numbers as `fNum(d)² · ‖W_d‖₂⁴ = ‖W_d‖₄⁴ · fDen(d)²` with `f(d) = fNum/fDen` — the exact clearing of denominators of `M₄(d)² = f(d)`, legitimate because `‖W_d‖₂² = 1 > 0` and both sides are positive, so `M₄(d)² = f(d) ⟺ M₄(d)⁴ = f(d)²`. At `d = 1` this is `9 = 8`, refuted. The conjecture's universal quantifier over `d` is captured by `Conj := ∀ d ≥ 1, Clause d`, and `conjecture_00000007739_false` negates the conjunction with an arbitrary second clause `C2`, which correctly handles the vague `M_∞/M_p` clause. Ambiguity of "which word" and of "optimal constant" (the Chinese text's 最优常数) is handled: at `d = 1` every word is a single semicircular with the same ratio, and `first_chaos_three`/`first_chaos_never_formula` prove the ratio `‖S‖₄⁴/‖S‖₂⁴` is identically 2 across the whole first chaos (a polynomial identity, valid over ℝ too), so supremum, infimum, and every attained value all give `M₄(1)⁴ = 2 ≠ 9/4, 3/2, 81/16`.

The report's mathematics beyond Lean is also correct and carefully hedged: the general `d` result `‖W_d‖₄⁴ = d+1` (up-sets of outer colours; Fuss–Catalan) matches my independent enumeration; the 2-adic valuation argument (`f(d)` has odd numerator, so `f(d)^k` is never an integer `d+1`) is valid; and the disclosed coincidence `‖1+s‖₄⁴/‖1+s‖₂⁴ = 9/4 = f(1)²` is honestly analyzed and correctly dismissed (1+s is not a word of length 1, and 9/4 is not the optimum of the non-centred family, which is 7/3).

## Issues found
None blocking. Lean verifies concrete instances (d = 1..4 for the words, three-letter first chaos, moments of X₀ up to degree 10); general `d`, complex coefficients, and the passage to the von Neumann algebra closure are correctly argued in the report and cross-checked in verify.py, and the disproof only needs `d = 1`, which is fully formalized.

## Verdict
APPROVED. The refutation is mathematically correct and fully formalized at the decisive case `d = 1` in self-contained core Lean 4 with only standard axioms; the formalization faithfully encodes the conjectured identity (including all plausible normalizations and the optimal-constant reading), and the report, Lean, verify.py, and my independent pairing enumeration all agree.
