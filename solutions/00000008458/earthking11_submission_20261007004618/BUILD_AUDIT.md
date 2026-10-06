# Verification audit

- Lean toolchain: `leanprover/lean4:v4.33.1` (Lean 4.33.1, arm64 Apple Silicon).
- Dependencies: no external packages; the proof imports `Std` from the pinned Lean toolchain. `lake-manifest.json` records an empty package list.
- `lake build`: passed on 2026-10-07, building `Main` successfully.
- `lake env lean Check.lean`: passed. `#print axioms` reports that both `Tlmc8458.no_stated_smallest_example` and `Tlmc8458.source_claim_false` do not depend on any axioms.
- A source scan found no uses of `sorry`, `admit`, `native_decide`, or user-declared axioms in the proof files.
- The Lean result proves the inconsistency of the single-width reading encoded in `Main.lean`; it does not formalize a distinction between reduced and unreduced Khovanov homology, which the source conjecture itself does not specify.
