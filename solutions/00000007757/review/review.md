# Solution Review — Conjecture 00000007757 (PR 828)

**Submission:** earthking11 — `earthking11_submission_20261007092550`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000007757.md` read in full (bilingual). The submission ships no `conjecture.md` copy (layout: solution.tex/.pdf, lean/, README.md, BUILD_AUDIT.md), so no byte-diff was possible; the write-up was instead checked clause by clause against the official text.
- LaTeX rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory; build clean. Shipped vs rebuilt PDF text compared with pypdf after whitespace normalization: content identical; differences are only fi/ff/ffi ligature and math-glyph extraction artifacts plus line-break spacing, all cosmetic.
- `lake build`: succeeded, zero errors, no warnings (2759 jobs). Toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474` (declared in lakefile and lake-manifest.json; linked against the prebuilt pool).
- Axioms: `#print axioms TLMC7757.infinite_common_periodic` in Main.lean, output confirmed in an independent rebuild: `depends on axioms: [propext, Classical.choice, Quot.sound]` — only the standard three. Grep for `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `axiom`, `set_option` over all shipped files: no hits other than the `#print axioms` line itself.
- Aux code: none shipped; none needed (the BUILD_AUDIT claims "no auxiliary computation", which is accurate).
- metadata.csv lists conjecture 00000007757 as unsolved; the submission is a disproof.

## Semantic audit

The official conjecture defines periodic-point spectral orthogonality for two distinct maps f, g ∈ Q(z) of degree ≥ 2 lying in a common commuting semigroup, with P_f, P_g their periodic-point sets on P^1(Q̄). Its first assertion is a universal claim: P_f ∩ P_g is finite, with cardinality controlled by a uniform function of deg f · deg g; a second clause asserts emptiness when the maps have no common iterate, decidable via weighted preperiodic-height identities.

The submission proves the negation of the first assertion by explicit counterexample: f(z) = z² and g(z) = z⁴ = f∘f. These are distinct rational maps over Q of degrees 2 and 4, and they commute on the entire projective line (both polynomial extensions fix ∞). For each n ≥ 0 it takes a primitive (2^(n+1)−1)-st root of unity ζ_n; since ζ_n^(2^(n+1)) = ζ_n and 4^(n+1) − 1 = (2^(n+1)−1)(2^(n+1)+1), ζ_n is periodic for both f and f∘f, and the strictly increasing orders make the ζ_n pairwise distinct. Hence P_f ∩ P_g is infinite while deg f · deg g = 8 is fixed — no uniform finite bound can exist. This is exactly the negation of the conjecture's universal finiteness claim: a counterexample satisfying all stated hypotheses (distinctness, degrees ≥ 2, commutation).

The Lean formalization is faithful to the conjecture's own objects. K = AlgebraicClosure ℚ is Q̄; P^1 is modeled by `Option K` with `some z` = [z:1] and `none` = [1:0]; F and G are the projective extensions of z², z⁴. The file proves the affine iterate formulas, commutation on all of P^1 (`commute_projective`), distinctness F ≠ G, and builds the infinite family via `witness n` (existence of primitive roots of unity in an algebraically closed field), `root_periodic_f`/`root_periodic_g`, `root_injective` (distinct primitive orders ⇒ distinct roots), and finally `infinite_common_periodic : Set.Infinite {x | Periodic F x ∧ Periodic G x}`, which is precisely infinitude of P_F ∩ P_G. Nothing is assumed, no toy surrogate is used, and the example is squarely within the conjectured class. The Scope paragraph is honest: the example deliberately has a common iterate; the conjecture's finiteness assertion does not exclude that case, and the no-common-iterate clause is irrelevant to the refutation.

The mathematics was sanity-checked independently: numerically, roots of unity of orders 1, 3, 7, 15, 31, 63, 127, 255 are periodic under both z² and z⁴, orders 2^(n+1)−1 strictly increase, and z⁴ = (z²)² as maps — exactly mirroring the Lean argument, which is elementary and complete.

## Issues found

None blocking. The submission ships no copy of the official conjecture text (noted above). The degree claims deg f = 2, deg g = 4 appear in Lean only as polynomial degrees of X² and X⁴ rather than through a formal rational-map degree, but the decisive theorem does not depend on them, and the arithmetic degrees are correct.

## Verdict

APPROVED. This is a correct, faithful, and complete disproof of the finiteness assertion of conjecture 00000007757 as written: two distinct commuting degree-≥2 rational maps over Q (z ↦ z² and z ↦ z⁴) share infinitely many periodic points in P^1(Q̄), so no finite uniform cardinality bound in deg f · deg g can exist. The build is clean, the axioms are exactly the standard three, the LaTeX matches, and the write-up scopes its claim honestly.
