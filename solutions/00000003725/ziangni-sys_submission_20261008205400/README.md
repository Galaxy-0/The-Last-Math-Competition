# Disproof of conjecture 00000003725

The actual star K1,4 has fourth adjacency spectral moment 32, while the
standard quasi-complete QC(5,4) has moment 28. Both have 5 vertices and
4 edges. Thus the prescribed quasi-complete graph fails to maximize
this genuine moment. The moment convention is trace(A^k), k = 4.

Complete report: proof.tex and compiled proof.pdf. Lean project: lean/,
Lean 4.19.0, Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
Reproduce: cd lean; lake update; lake build. Report: tectonic proof.tex.

Validation: one successful final full lake build after a draft Sym2 case
label repair. Nine audits use only propext/Classical.choice/Quot.sound,
with canonical integer parameters axiom-free. The PDF compiled cleanly
after a draft line-wrap fix; one page rendered and visually inspected.
Actual SimpleGraph edge sets, real adjacency matrices and fourth-power
traces are certified. No numerical oracle. Local caches are ignored.

The standard quasi-complete construction is independently documented in
Abrego et al., Sum of squares of degrees in a graph (2009), Section 1:
https://emis.de/ft/14223
