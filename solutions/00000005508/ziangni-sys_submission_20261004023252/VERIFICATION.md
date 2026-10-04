# Verification evidence

Verified on 2026-10-04 with Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

## Semantic scope

The source English and Chinese texts both claim the minimum-residual-capacity multiplicity is at most the logarithm of the number of stations. A one-station network is permitted by their wording. Its positive capacity and traffic coefficient are both 1. The formal model proves saturation exactly for loads at least 1, no earlier saturation, a first-bottleneck cardinality of 1, and a minimum-residual-capacity multiplicity of 1 at every load. These independently computed counts agree at saturation.

The universal natural-logarithm bound is false. The supplementary base-change theorem proves the same witness for all genuine logarithm bases. The report's two-station discussion is illustrative; the singleton counterexample alone is the formal disproof.

## Formal checks

- Project-local build products were removed, without traversing dependency junctions, before a fresh build.
- lake build: successful.
- lake env lean Main.lean: successful.
- Final theorem axiom audits: exactly propext, Classical.choice, Quot.sound. No sorryAx or extra axioms.
- No sorry, admit, native_decide, or axiom declarations are present in the submitted Lean source.
- Pinned dependency manifest contains Git revisions only; ignored local junctions are not part of the submission.

## Report checks

- Built-in editor opened report.tex. Its compiler returned the platform-directory lookup failure documented in the run protocol.
- Tectonic compiled the actual report.pdf successfully, with no overfull boxes or unresolved references.
- Poppler confirmed a one-page A4 PDF.
- The complete final PDF page was rendered to PNG and visually inspected: no clipped text, overlap, missing glyphs or margin overflow.

## Auxiliary code and repository scope

No computational auxiliary proof is required.
Only the personal submission directory is committed.
git diff --check passed.
