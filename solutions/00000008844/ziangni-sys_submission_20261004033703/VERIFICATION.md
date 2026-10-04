# Verification evidence

Validated on 4 October 2026 with Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

- Fresh submission project: `lake build` completed successfully (1662 build jobs).
- Direct source check: `lake env lean Main.lean` completed successfully.
- The printed axiom dependencies of `firm_graph`, `graph_iff_value`, `resolvent_firm`, and `fixed_set_eq_zero_set` are exactly `[propext, Classical.choice, Quot.sound]`.
- Lean defines actual set-valued monotonicity, the inverse graph of I + lambda A, its natural domain, and a choice-defined map. It proves graph membership and uniqueness rather than assuming them.
- The firm inequality holds for all pairs of domain inputs. The fixed-point set, regarded as a subset of the ambient space, is exactly the operator's zero set for every positive parameter.
- No completeness, maximality, or totality assumption is used. The positive parameter and natural-domain convention are explicitly stated in the report.
- No `sorry`, `admit`, `native_decide`, or additional axioms occur in the proof.
- Tectonic compiled the included one-page A4 PDF successfully. Poppler rendered the entire page, which was visually inspected: formulas, paragraphs, margins, and footer are legible without clipping or overlap.
- The built-in LaTeX compiler was attempted and encountered its known platform-directory lookup error; the included PDF was produced by Tectonic.
- Dependency caches and local junctions are excluded from the submission. Text sources use LF line endings.
