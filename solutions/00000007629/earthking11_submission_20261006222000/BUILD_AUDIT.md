# Reproducible build and semantic audit

- Toolchain: `leanprover/lean4:v4.33.1`.
- Mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474`.
- The included manifest pins all dependencies. From `lean/`, run `lake build`.
- Independent parent-agent build succeeded. All five printed theorem audits
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- No unfinished proof, native evaluation, or additional axiom is used.
- No brute-force search is required.

The formal capstone contains the actual quadratic form, orthonormal basis,
two distinct members of Mathlib's spin group, their Clifford conjugation on
every vector, preservation of the quadratic form and basis, determinant 1,
and the negation of unique rotor realization. This is not just a numerical
sign identity or an action of an artificially defined two-element group.
The source does not identify opposite rotors. The conclusion does not apply
to uniqueness after quotienting by the central sign.
