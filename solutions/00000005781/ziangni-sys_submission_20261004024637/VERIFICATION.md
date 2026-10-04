# Verification evidence

Date: 2026-10-04. Lean: 4.19.0. Mathlib: pinned commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

## Mathematical correspondence

The actual real potential is x²/2; its derivative is proved to be x and its Hessian 1. Strict convexity is proved by the exact positive Jensen gap. The Legendre dual maximum is proved by an upper bound valid for every primal coordinate and equality at x = eta.

The canonical divergence is defined by the primal-dual potential formula using the actual derivative operator, then proved equal to the Bregman formula and squared distance over two. The original dually flat structure is the line with constant metric 1 and zero connection coefficients in both coordinates. This coordinate interpretation is established in the report; no general manifold theory is asserted as formalized.

The signed triangle identity is proved for all real triples. Distinct triples (0,1,2) and (0,2,1) disprove universal nonnegativity in either sign convention. No source orthogonality or projection hypotheses were omitted: neither bilingual statement has them.

## Checks

- Fresh project lake build: passed, 1790 targets, final source without tactic warnings.
- Direct lake env lean Main.lean: passed.
- Both final negations, Hessian and strict-convexity theorems have only standard axiom dependencies: propext, Classical.choice, Quot.sound.
- No sorry, admit, native_decide or added axioms.
- The public manifest pins Git revisions, never local paths. Local dependency junctions and build products are ignored.
- Built-in editor opened the source. Built-in compiler returned its known platform-directory error; Tectonic successfully compiled the deliverable PDF.
- Final Tectonic output had no overfull-box or reference warnings.
- Both final A4 PDF pages were rendered with Poppler and visually inspected; no clipping, overlap, missing glyphs, or broken paragraphs.
- No auxiliary computational proof is required.
- git diff --check passed; committed files are restricted to this personal submission.
