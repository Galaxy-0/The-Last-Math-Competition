# Solution Review — Conjecture 00000002450 (PR 750)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005204011`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (`conjectures/00000002450.md`, bilingual); shipped `conjecture.md` is **byte-identical** to it (`diff` empty).
- **LaTeX**: full `proof.tex` read; independent `latexmk -pdf -interaction=nonstopmode` rebuild succeeds (exit 0). Shipped vs rebuilt PDF text compared with pypdf after normalization: content matches; residual diffs are glyph-extraction artifacts of the author's MiKTeX fonts (e.g. ∃ extracted as 9, braces as f/g) versus the rebuild — cosmetic. One cosmetic source typo noted under Issues.
- **Lean build**: `lake build` completes with **zero errors and zero warnings** (8708 jobs). Toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360ea`, prebuilt pool.
- **Axioms**: independent `#print axioms` for `C2450.exists_nondiscrete_allSmooth_polishGroup`, `C2450.allSmooth_of_compact`, and `C2450.cantor_not_discrete` each reports exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, `admit`, `unsafe`, `extern`, `implemented_by`, or declared `axiom`.
- **Aux code**: `verification/axioms.txt` matches my independent run verbatim; `verification/build.txt` consistent with the fresh build; `SHA256SUMS.txt` mismatches fully explained as CRLF-vs-LF hashing artifacts (LF→CRLF re-hash reproduces each recorded value; shipped content identical).
- **Metadata**: `metadata.csv` lists 00000002450 as unproven and undisproven; no solution folder for it on `main`.

## Semantic audit

The conjecture is a bare existential: there is a Polish group G that is nondiscrete while all of its Borel-action orbit equivalence relations are smooth. The submission proves exactly this statement, with the decisive theorem `exists_nondiscrete_allSmooth_polishGroup` proving the existence of G with the standard structure (Group, topological group, Polish space, Borel σ-algebra), ¬DiscreteTopology G, and AllSmooth G — where `AllSmooth` quantifies over every standard Borel space in an arbitrary universe and every Borel action (genuine `MulAction` whose action map is jointly measurable; no continuity assumed), and `IsSmooth` is the textbook definition (a Borel map into a Polish space whose fibers are exactly the equivalence classes). The witness is the Cantor group (ℤ/2)^ℕ: Polish as a countable product of finite discrete groups, and nondiscrete because a compact discrete space is finite while this group is infinite.

The content is the general theorem `allSmooth_of_compact`: every compact Polish group is all-smooth. This is a classical fact of invariant descriptive set theory, and the self-contained proof is correct. The complete invariant f(x) = (μ{g : e(g⁻¹·x) < q})_{q∈ℚ} uses a Borel embedding e of X into ℝ and Haar measure μ; f is Borel by Fubini measurability for the fixed q-sections, invariant because g⁻¹h·x = (h⁻¹g)⁻¹·x turns the measure into a left translate and Haar is left-invariant (and finite and nonzero since G is compact). If f(x) = f(y) but the orbits differ, the orbits are disjoint analytic sets, so Lusin separation yields a Borel A ⊇ Gx with Gy ∩ A = ∅; the pushforward measures of μ under g ↦ e(g⁻¹·x) and g ↦ e(g⁻¹·y) agree on the rational half-lines (which form a π-system generating Borel(ℝ), with total masses checked) hence are equal — but the first assigns mass μ(G) > 0 to e(A) (every g⁻¹·x lies in A) and the second assigns 0 (injectivity of e plus orbit disjointness), a contradiction. Compactness is used exactly where it is needed (finite positive Haar mass); for non-compact groups the statement would be false (E₀ is a countable discrete group's orbit equivalence relation), so the witness class is not an artifact.

I checked the argument step by step against the Lean source — the measure-pushforward equality via `ext_of_generate_finite` on `Real.isPiSystem_Iio_rat`, the analytic-set images, the ENNReal.toReal finiteness handling, the compact/infinite contradiction for nondiscreteness — and find no gap. The conjecture is true and this is a faithful proof of it; the report matches the Lean development, and the SEMANTIC_REVIEW's additional claims (uncountability, actions with uncountably many orbits) are correct though immaterial to the existential.

## Issues found

None blocking. (Cosmetic: `proof.tex` line 52 contains a literal TAB character where `\times` was intended, so one inline formula in a remark renders as "CimesC" in the shipped PDF; the shipped PDF faithfully matches its source, and the sentence remains readable. Not a content discrepancy.)

## Verdict

APPROVED. The submission proves the conjecture's exact statement with a correct, classical, fully self-contained argument (compact Polish groups are all-smooth; the Cantor group is a nondiscrete witness), formalized faithfully over the real objects (Polish groups, standard Borel spaces, Haar measure, Lusin separation), compiling cleanly with only the three permitted axioms and with report and Lean in agreement.
