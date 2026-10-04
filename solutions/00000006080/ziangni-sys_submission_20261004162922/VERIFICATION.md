# Validation

The final full lake build succeeds, including Main. Twelve axiom audits cover actual network evaluation, the Fréchet derivative, all local/global minima and their values, actual Hessian entries and full spectra, criticality, unequal spectra, the perturbation, strict saddles and the existential solution. Only standard propext/Classical.choice/Quot.sound occur; no added axioms or sorryAx.

All matrix spectra concern actual second derivatives of actual network output functions, connected by the proved network polynomial identity. Every c>0 is covered by the complete local/global minimum theorems. The origin is excluded as a local minimum by a descent point in every neighborhood.

Tectonic compiled the two-page report.pdf (41,031 bytes). Long formal-name line breaks were repaired; the final compile has no box warnings, and both final rendered pages were visually inspected without clipping or overlap. The built-in editor/compiler was attempted and encountered its platform-directory error; the existing Tectonic compiler supplied the PDF.

Public Lean4.19.0/Mathlib pins permit reproduction without local cache junctions. No shared cache extension was needed. Text is UTF-8 LF and the scoped diff check passes. The source leaves the activation class unrestricted; this proof explicitly uses square activation.
