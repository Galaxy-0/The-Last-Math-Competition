# Verification

The completed submission uses Lean 4.19.0 and pinned Mathlib v4.19.0. `lean-build.txt` records a fresh local project build; `lean-check.txt` records a direct complete-source recheck with warnings treated as errors and four theorem axiom audits. All audited dependencies are only propext, Classical.choice and Quot.sound. No auxiliary numerical code is necessary: every Bernoulli recurrence evaluation and rational inequality is kernel checked.

`pdf-build.txt` records successful Tectonic compilation. The built-in LaTeX editor was opened and its compiler was attempted, but returned the known platform standard-directory lookup error; the actual final PDF was generated successfully with Tectonic. Both A4 pages were rendered with Poppler at 1400 pixels and visually inspected in full: readable formulas and tables, no overlap or clipping. There are no TeX overfull/underfull box warnings.

`source.md` preserves the bilingual statement. `eligibility.txt` records initial metadata, source-path and all-state PR checks. The root coordinator repeats live eligibility checks before publication.

Semantic scope: the explicit displayed rational finite-group-order equality is impossible, as are the absolute-value and indicated parenthetical fraction readings. We compute the actual Mathlib Bernoulli number; we do not compute algebraic K-theory or replace an unspecified integrality operation by a definition.
