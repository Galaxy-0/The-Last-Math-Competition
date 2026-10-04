# Validation

The final whole-project lake build succeeds with Lean 4.19.0 and the pinned public Mathlib dependency. Eight printed axiom audits cover connectivity, edge counts, the spectrum/determinant bridge, both full spectra, both radii, and the final counterexample. Only propext, Classical.choice and Quot.sound occur; no sorryAx or added axioms.

The proof uses actual graph adjacency matrices and Mathlib spectrum, rather than assumed eigenvalue certificates. Both connected graphs are on Fin 3. The edge representatives i<j count undirected edges once.

Tectonic compiled report.tex into a two-page report.pdf (39,572 bytes). Both rendered pages were visually inspected: equations and prose are readable with no clipping or overfull boxes. The built-in editor compiler was attempted but encountered its known platform-directory error; the existing Tectonic compiler supplied the PDF.

The disproof addresses the source's unrestricted maximal-radius clause. No fixed-edge or tree hypothesis is assumed, and the separate neighborhood clause is not needed.
