# Disproof of conjecture 00000008782

For the actual real matrix [[0,1],[-1,0]], the one-sample Hutchinson estimator zᵀAz vanishes at every vector. Its variance under genuine independent Rademacher coordinates is zero, whereas the displayed expression 2(||A||F²−Σaii²) equals four.

Both original languages omit a symmetry hypothesis. This is a counterexample to the unqualified variance assertion, not to the usual symmetric-matrix formula. Other Hutch++ and probing conjuncts are not required for the disproof.

report.tex/report.pdf explain the full argument and the missing hypothesis. lean/Main.lean constructs a probability mass function on four outcomes and its actual measure, proves actual IndepFun and Rademacher marginal laws, and computes the genuine quadratic form, Bochner expectation, Mathlib variance, trace and Frobenius norm. verification/ records source and validation.

From lean/, using Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

Mathlib is publicly pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Local ignored cache junctions are not submitted. No custom axioms, admitted proofs or native decision procedures are used.

The built-in LaTeX editor/compiler was attempted; its platform-directory error was handled by successful Tectonic compilation. Every final PDF page was rendered and visually inspected.
