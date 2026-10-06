# Verification audit

- Lean toolchain: `leanprover/lean4:v4.33.1` (Lean 4.33.1, arm64 Apple Silicon).
- Dependencies: no external packages; only `Std` from the pinned Lean toolchain is imported. `lake-manifest.json` records an empty package list.
- `lake build`: passed on 2026-10-07, building `Main` successfully.
- `lake env lean Check.lean`: passed. `#print axioms` reports that `Tlmc8304.finite_count_conflicts_with_threshold`, `Tlmc8304.source_claim_false`, and the evaluation `Tlmc8304.stated_count_at_24` do not depend on any axioms.
- A source scan found no uses of `sorry`, `admit`, `native_decide`, or user-declared axioms in the proof files.
- The formalization treats the breakpoint set consistently as `Breakpoints n` in both clauses and uses the same natural-number parameter `n`; no facts about symplectic geometry are assumed.
