# Solution Review — Conjecture 00000007766 (PR 829)

**Submission:** earthking11 — `earthking11_submission_20261007100400`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000007766.md` read in full (bilingual). The submission ships no `conjecture.md` copy (layout: solution.tex/.pdf, lean/, README.md, BUILD_AUDIT.md), so no byte-diff was possible; the write-up was checked clause by clause against the official text.
- LaTeX rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory; build clean. Shipped vs rebuilt PDF text compared with pypdf after whitespace normalization: content identical; differences are only ff/fi ligature and math-glyph extraction artifacts (∈, ∞, →, ⊆ extracted as surrogate codepoints) plus line-break spacing, all cosmetic.
- `lake build`: succeeded, zero errors, two harmless linter style warnings ("let is preferred over letI" at Main.lean:16, "have is preferred over haveI" at Main.lean:21) (2499 jobs). Toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474` (declared in lakefile and lake-manifest.json; linked against the prebuilt pool).
- Axioms: `#print axioms TLMC7766.no_claimed_value_set` in Main.lean, output confirmed in an independent rebuild: `depends on axioms: [propext, Classical.choice, Quot.sound]` — only the standard three. Grep for `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `axiom`, `set_option` over all shipped files: no hits other than the `#print axioms` line itself.
- Aux code: none shipped; none needed (BUILD_AUDIT's "no auxiliary computation" is accurate).
- metadata.csv lists conjecture 00000007766 as unsolved; the submission is a disproof.

## Semantic audit

The official conjecture defines the local gap of canonical heights, D(x) = ĥ_f(x) − ĥ_{f^∨}(x) for a rational map f and its dual, and asserts (English and Chinese texts agree) that on periodic points D takes discrete values with value set consisting of 0 and all reals at least some explicit positive constant c — i.e. value set = {0} ∪ [c, ∞) — plus a separate t^(−1/2) tail-asymptotic claim. The value-set clause is the load-bearing combinatorial claim, and it is stated as an equality of the range of D on periodic points.

The submission proves the exact negation, stronger than required: for every self-map F of P^1(Q̄), every function D : P^1(Q̄) → ℝ, and every real c, D(Per(F)) ≠ {0} ∪ [c, ∞). The argument is a cardinality obstruction intrinsic to the conjecture's own setting: Q̄ = AlgebraicClosure ℚ is countable (each element algebraic over the countable field Q, countably many polynomials, finitely many roots each), hence P^1(Q̄) (modeled as `Option K`) is countable, so Per(F) and its image under D are countable; while [c, ∞) is uncountable via the injection x ↦ c + e^x. Since the conjecture's D — whatever the dual-map convention — is a real-valued function on these periodic points, the claimed value set is impossible. Note also the stated claim is internally inconsistent (a set containing the ray [c, ∞) is not discrete), which corroborates that the value-set clause as written cannot hold.

The Lean formalization is faithful and avoids both faithfulness failure modes: nothing is assumed (the theorem has only universally quantified hypotheses F, D, c) and no toy instance is used — because the refutation holds for all F, D, c, it applies in particular to the canonical-height gap on the conjecture's own objects, using only the fact that its periodic points live in the countable P^1(Q̄). The countability of K is derived honestly from `Algebra.IsAlgebraic`/`Algebraic.countable`, and `uncountable_upper_ray` from the exponential injection. The decisive theorem `no_claimed_value_set` states precisely ¬(D '' Per(F) = {0} ∪ Ici c); instantiating at the conjecture's D and c gives the negation of the conjecture's value-set assertion, which as one conjunct of a conjunction defeats the conjecture. The Scope paragraph honestly limits the claim: the separate tail-asymptotic clause is not analyzed, and no such analysis is needed to refute the conjunction.

The mathematics was sanity-checked independently: countability of Q̄ and of P^1(Q̄), countable image, and uncountability of [c, ∞) are standard, and the specific injections used in the Lean proofs (exp into the upper ray, arctan-free here) are correct and correctly composed (preimage of the range under an injection is the full domain).

## Issues found

None blocking. No conjecture.md copy shipped (noted above). The two linter warnings are stylistic only.

## Verdict

APPROVED. This is a correct, faithful disproof of the value-set assertion of conjecture 00000007766: the periodic points of any self-map of P^1(Q̄) form a countable set, so no real-valued height gap — canonical or otherwise — can attain every real value at least c in addition to 0. The universal form of the Lean theorem makes the refutation airtight against any convention for the dual map or the constant, the build is clean, the axioms are exactly the standard three, and the write-up matches the shipped PDF and scopes its claim honestly.
