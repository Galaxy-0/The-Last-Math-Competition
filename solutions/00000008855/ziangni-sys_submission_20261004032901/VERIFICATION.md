# Verification evidence

Validated on 4 October 2026 with Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

- Fresh submission project: `lake build` completed successfully (745 build jobs).
- Direct source check: `lake env lean Main.lean` completed successfully.
- The printed axiom dependencies of `prox_two_iff`, `prox_one_iff`, and `conjecture_8855_false` are exactly `[propext, Classical.choice, Quot.sound]`.
- The proof defines the scalar nonzero-count penalty, quadratic objective, universal global-minimum relation, and piecewise soft threshold. Both unique-minimum characterizations quantify over every real competitor.
- No fixed nonnegative soft threshold represents this penalty's proximal map at unit proximal parameter. This disproves the first clause of the original conjunction; no splitting convergence-rate claim is needed or asserted.
- No `sorry`, `admit`, `native_decide`, or extra axioms occur in the Lean source.
- Tectonic compiled `report.tex` successfully into the included one-page A4 PDF. Poppler rendered the entire page, which was visually inspected: formulas, text, margins, and footer are legible without clipping or overlap.
- The built-in LaTeX compiler was attempted but failed with its platform-directory lookup error; the included PDF was produced by Tectonic.
- Dependency build caches and local junctions are ignored and excluded from the submission. Source files use LF line endings.

The penalty is nonconvex. The source conjecture does not impose convexity; the report explicitly identifies this scope. The scalar absolute-value penalty's usual soft-threshold formula is not claimed to fail.
