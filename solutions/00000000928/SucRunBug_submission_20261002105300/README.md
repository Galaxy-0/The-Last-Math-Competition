# Conjecture 00000000928 - disproof

Submitter: [SucRunBug](https://github.com/SucRunBug). AI-assisted mathematical work and Lean formalization.

The density and absence-of-invariant-subspace conditions are incompatible for a bounded complex Hilbert-space operator. Every nonzero eigenspace is closed and invariant. If there is no nonzero proper closed invariant subspace, every eigenvalue has the entire space as its eigenspace; there can therefore be at most one eigenvalue, precluding density on the unit circle.

The argument establishes a stronger statement on all complex normed spaces. It uses the standard bounded-operator and nonzero proper closed-subspace convention of the invariant subspace problem. It does not purport to resolve that general problem.

## Contents

- `main.tex`: complete mathematical proof.
- `main.pdf`: readable rendering of the same complete proof; it is not a native-preview export. The LaTeX source is independently checked with the native compiler.
- `lean4/`: pinned Lean 4/Mathlib v4.33.0 project. Mathlib commit: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- `verification.txt`: actual successful compilation and axiom-check outputs plus source hashes, recorded before publication.

## Reproduction

In `lean4/`, run `lake exe cache get`, `lake build`, and `lake env lean Check.lean`.

`pointSpectrum` uses Mathlib's `Module.End.HasEigenvalue`, which requires a nonzero eigenvector. `HasClosedInvariantSubspace` explicitly requires closedness, nonzero, properness, and invariance. `DensePointSpectrumOnCircle` requires every unit-circle point to belong to the closure of the point spectrum, a weaker condition than the filed density assertion. The checked theorem derives an actual submodule satisfying all four requirements. Refuting the density/no-invariant-subspace conjunction refutes the additional whole-disk assertion as well.

Only standard Lean foundations are used; there are no incomplete proofs, custom axioms, or `native_decide`. Official acceptance and leaderboard attribution require organizer review.
