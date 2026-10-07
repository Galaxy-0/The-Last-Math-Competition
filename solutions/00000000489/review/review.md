# Solution Review — Conjecture 00000000489 (PR 781)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005232524`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** DISPROOF. **Conjecture:** third-order character sum.

## Checklist results

- **Official conjecture.** `conjectures/00000000489.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The conjecture asserts S₃(n) = ∑_λ f_λ³/n! = Θ(√(n!)·n^{1/4}) with main-term constant 2^{1/4}π^{−1/2}. The submission proves the truth is the opposite extreme: S₃(n) ≤ √(n!) for every n, so S₃(n)/(√(n!)·n^{1/4}) ≤ n^{−1/4} → 0. The engine is the Bessel-type bound ∑ f_λ² = n! for pairwise non-isomorphic irreducible complex representations of a finite group, proved self-containedly: χ(g⁻¹) = conj χ(g) via the invariant positive definite matrix P = ∑_h A(h)^H A(h); orthonormality from `FDRep.char_orthonormal`; then with Φ = ∑ dᵢχᵢ and D = ∑ dᵢ², ∑_g Φ(g)Φ(g⁻¹) = |G|·D and |Φ(1)|² = D² ≤ |G|·D give D ≤ |G|. Then each f_λ ≤ √(n!) and ∑ f_λ³ ≤ √(n!)·n!. The formal refutation kills all three components of the statement: ¬Θ (little-o plus `isLittleO_irrefl`), the ratio does not tend to 2^{1/4}π^{−1/2} (it tends to 0), and the asymptotic-equivalence clause fails.

A semantic subtlety is handled in the safe direction: the conjecture's f_λ are the Specht-module dimensions, while the Lean theorem quantifies over every labelled family of pairwise non-isomorphic irreducibles indexed by the partitions of n (`IrrepFamily`). Since the universal statement implies the Specht instance (whose existence is classical and cited from the standard reference), and since the proof uses only facts true of the Specht family, this is a strengthening, not a loophole; the report says exactly this. The three readings refuted (Θ-claim, limit constant, asymptotic equivalence) are precisely the components of the bilingual text; the garbled Chinese prefix and the interpretive '3-thread counting of the limit shape' are declared out of scope rather than quietly redefined.

I verified the bound on small cases (n = 3: S₃ = 3/6 = ½; n = 4: S₃ = (1+1+8+1)/24 = 11/24; both far below √(n!)) and the ratio decay n^{−1/4}. The character-theory argument is the standard one and each step is machine-checked, including the eventual nonvanishing of g(n) needed for the Θ-refutation.

## Issues found

Minor, disclosed: the Specht family itself is not constructed in Lean; immaterial because the theorem is universally quantified over irreducible families. No fix required.

## Verdict

APPROVED. A decisive disproof: the true size of S₃(n) is at most √(n!), so the conjectured Θ(√(n!)·n^{1/4}) growth, its limit constant, and its asymptotic-equivalence phrasing are all false, with the quantification over irreducible families done in the safe (stronger) direction.
