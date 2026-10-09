# Validation

- Full `lake build` completed successfully with Lean 4.19.0 and pinned Mathlib. Only optional style suggestions were emitted.
- The printed audits for independence, law, positivity, second moments, exponential moments, exact passage time, variance and final negation use only `propext`, `Classical.choice`, and `Quot.sound`.
- The proof has no placeholders, native evaluation, custom axioms or unsafe declarations.
- `passage_eq_distance` proves that the real infimum is meaningful: an explicit horizontal walk attains n, and every lattice walk costs at least n. The final theorem does not assume a shortest-path certificate or a variance identity.
- Tectonic compiled the final report; both pages were rendered with Poppler and visually checked for readable text and formulas, intact margins and correct page flow. The native editor's compiler was unavailable because of a platform standard-directory error.
- Local build-cache junctions are ignored. The submitted dependency manifest uses public Git repositories and exact revisions.
