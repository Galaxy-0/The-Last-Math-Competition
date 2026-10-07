# Verification record

- Lean toolchain: `leanprover/lean4:v4.33.1`.
- `cd lean && lake build`: passed (3 Lake jobs).
- `Main.lean` contains no `sorry`, `native_decide`, or `axiom` declarations.
- `TECTONIC_CACHE_DIR=.tectonic-cache tectonic --keep-logs -o . main.tex`: exit code 0; wrote `main.pdf` (one US Letter page).
- `pdfinfo main.pdf`: one page, PDF 1.5.
- `pdftotext main.pdf -`: extracted all three sections and the complete proof text.
- Rendered page 1 with `pdftoppm` and visually checked margins, equations, line breaks, and page number; no clipping or overlap found.

The Lean result is an internal inconsistency proof, not a computation of the sphere-spectrum THH groups. See `README.md` for the exact formalization boundary.
