# Solution Review — Conjecture 00000003480 (PR 830)

**Submission:** earthking11 — `earthking11_submission_20261007101400`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000003480.md` read in full (bilingual). The submission ships no `conjecture.md` copy (layout: solution.tex/.pdf, lean/, README.md, BUILD_AUDIT.md), so no byte-diff was possible; the write-up was checked clause by clause against the official text.
- LaTeX rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory; build clean. Shipped vs rebuilt PDF text compared with pypdf after whitespace normalization: content identical; differences are only ff/fi ligature and math-glyph extraction artifacts (≥, −, →, ⊆ extracted as surrogate codepoints) plus line-break spacing, all cosmetic.
- `lake build`: succeeded, zero errors, no warnings (2034 jobs). Toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360eaa60ab8c11dca51a86af692955474` (declared in lakefile and lake-manifest.json; linked against the prebuilt pool).
- Axioms: `#print axioms TLMC3480.no_full_interval_of_difference` in Main.lean, output confirmed in an independent rebuild: `depends on axioms: [propext, Classical.choice, Quot.sound]` — only the standard three. Grep for `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `axiom`, `set_option` over all shipped files: no hits other than the `#print axioms` line itself.
- Aux code: none shipped; none needed (BUILD_AUDIT's "no auxiliary computation" is accurate).
- metadata.csv lists conjecture 00000003480 as unsolved; the submission is a disproof.

## Semantic audit

The official conjecture connects the fractional chromatic number with the linear-programming dual of independence constraints (the fractional Hall bound) and asserts a "continuous spectrum": the difference χ_f − H_f takes every real value from zero to one, with the realizing family of Mycielski interpolation type and endpoint 1 attained only by finite approximations of infinite families. The first clause — surjectivity of the difference onto [0, 1] — is the essential claim, and it is a universal coverage statement over graphs.

The submission proves the exact negation: for any two real-valued functions on the class of finite simple graphs, the range of their difference cannot cover [0, 1]. The obstruction is countability of the domain, intrinsic to the conjecture's own objects: on a labeled n-vertex set there are at most 2^(C(n,2)) simple graphs, so the disjoint union Σ n : ℕ, SimpleGraph (Fin n) of all finite labeled simple graphs is countable, hence the image of the difference function is a countable subset of ℝ, while [0, 1] is uncountable (injected by x ↦ (arctan x + π/2)/π). This applies verbatim to the conjecture's invariants: fractional chromatic number and LP-dual Hall bounds are defined on finite graphs, and the conjecture's own Mycielski language (the Mycielski construction acts on finite graphs; "finite approximations of infinite families" are finite graphs) confirms that the intended domain is finite simple graphs. Over any domain of finite graphs — labeled or up to isomorphism, any family whatsoever — the range is a sub-range of a countable set and cannot be all of [0, 1].

The Lean formalization is faithful and avoids both faithfulness failure modes: the decisive theorem `no_full_interval_of_difference` quantifies over arbitrary real-valued `fractionalChromatic`/`fractionalHall` functions on `FiniteGraph := Σ n : ℕ, SimpleGraph (Fin n)`, so nothing about the deep LP theory is assumed as a hypothesis, and there is no toy surrogate — the countable-domain fact used is a property of the conjecture's own graph class, and the arbitrary-function generality subsumes the genuine invariants regardless of their exact LP definitions. The countable instance for the sigma type and the uncountability of Icc 0 1 are both proved in the file (the latter via the arctan injection with correct injectivity and range-in-(0,1) arguments). Instantiating the theorem at the conjecture's two invariants yields precisely ¬([0,1] ⊆ range of the difference), the negation of the continuous-spectrum clause, which as a conjunct defeats the conjecture. The Scope paragraph honestly delimits the refutation to finite unweighted graphs and does not claim anything about the endpoint-1 clause, none of which is needed.

The mathematics was sanity-checked independently: 2^(C(n,2)) graphs per n is elementary, countable union of finite sets is countable, and (arctan x + π/2)/π is a strictly increasing bijection ℝ → (0, 1), hence [0,1] is uncountable — exactly mirroring the Lean argument, which is elementary and complete.

## Issues found

None blocking. No conjecture.md copy shipped (noted above). The theorem is stated for arbitrary real-valued functions rather than the named invariants; this is a strengthening (valid for all instantiations), not a trivialization, since the decisive domain fact — countability of finite graphs — is proved for the actual graph class.

## Verdict

APPROVED. This is a correct, faithful disproof of the continuous-spectrum assertion of conjecture 00000003480: there are only countably many finite simple graphs, so the difference of the fractional chromatic number and any fractional Hall bound has at most countably many values and can never take every value in the uncountable interval [0, 1]. The build is clean, the axioms are exactly the standard three, the LaTeX matches the shipped PDF, and the write-up scopes its claim honestly to the standard finite-graph setting of the Mycielski family.
