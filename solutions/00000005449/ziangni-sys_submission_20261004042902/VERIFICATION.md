# Verification

## Mathematical scope

Both source versions assert a single-check detection lower bound of 1/2 at noncommutative witnesses. The experiment here draws two independent uniform elements from the symmetry group of the square and detects precisely when xy differs from yx. This is the standard commutativity spot-check named in the definition. The package refutes that lower-bound clause; it does not characterize unspecified alternative algorithms or the other automorphism clauses.

## Lean

- Lean 4.19.0; Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b, pinned in public configuration.
- Fresh local project lake build: success, 1180 build jobs; final rebuild after adding single-draw normalization: success.
- Direct whole-source lake env lean Main.lean -DwarningAsError=true: exit 0.
- Actual Mathlib DihedralGroup 4 multiplication and finite enumeration; ordinary kernel-checked decide proves group cardinality 8, pair cardinality 64, noncommuting witness, 24 detected pairs, and 40 commuting pairs.
- Uniform draw masses sum to 1. Joint masses are their product, nonnegative, and sum to 1. Detection probability is the sum over the actual finite event and equals 3/8, strictly below 1/2.
- Printed dependencies of the witness: propext, Quot.sound. Printed dependencies of the count, normalization, probability, and final theorem: propext, Classical.choice, Quot.sound. No sorry, admit, native_decide, or additional axioms.
- Shared targeted Dihedral cache extension completed successfully before building; dependency versions unchanged. Local ignored dependency junctions are not public configuration.

## PDF

- PDF artifact creation marker executed before report creation.
- Native LaTeX editor opened; its compiler failed platform-directory lookup (Unable to find standard directories for platform).
- Installed Tectonic compiled report.tex successfully without overflow warnings.
- Poppler pdfinfo: one A4 page, 32,529 bytes, PDF 1.5.
- Rendered the complete page at 130 dpi and inspected it visually: readable equations/table, no clipping, overlap, or orphan page.

## Repository

Only this submission directory is committed. Text files use LF; caches and build products are ignored. git diff --cached --check passed before commit.
