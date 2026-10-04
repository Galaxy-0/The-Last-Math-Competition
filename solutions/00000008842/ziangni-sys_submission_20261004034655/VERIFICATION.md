# Verification evidence

Validated on 4 October 2026 with Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b.

- Fresh project build and final revised `lake build` succeeded (1812 jobs).
- Direct final `lake env lean Main.lean` succeeded.
- All six printed theorem audits use exactly `[propext, Classical.choice, Quot.sound]`, including both complete `conjecture_8842` instances, the generic closedness theorem, and the generic dense-range theorem.
- Maximality is actual graph maximality under inclusion, without assumed closedness. The compatibility proof adjoins one point and derives the exact intersection-of-closed-sections representation.
- The normed-space instance uses the actual continuous dual and its continuous evaluation pairing. The inner-product-space instance uses the actual inner product. Both include the usual Banach/Hilbert settings; completeness is unnecessary.
- Domain density is the actual DenseRange of the canonical inclusion from the domain subtype to its closure subtype, proved for every topological set.
- No `sorry`, `admit`, `native_decide`, or extra axioms occur in the Lean source.
- Tectonic compiled the final included one-page A4 PDF (32117 bytes). Poppler rendered the complete final page, which was visually inspected for formula readability, layout, and clipping.
- The built-in LaTeX compiler was attempted and encountered its known platform-directory lookup failure; Tectonic produced the included PDF.
- Text sources use LF. Dependency caches and local junctions are ignored and excluded from the submission.
