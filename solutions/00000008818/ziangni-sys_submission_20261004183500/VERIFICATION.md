# Verification

- Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Final full `lake build` passed 1926 targets after development algebra and simplification repairs. One harmless unnecessary-sequence-focus linter warning remains.
- Fourteen printed axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.
- No sorry, admit, native_decide, unsafe declarations, or custom axioms.
- Formal coverage: global smoothness and strict convexity of x^4; actual derivative 4x^3; unique attained global minimizer; vanishing Hessian; actual IVT root r with bounds; positive Hessian estimates; scalar specialization of the complete Hessian BFGS formula; secant equation and positive curvature; actual search direction and iterate equation; Armijo and strong Wolfe tests; convergence to zero and failure of the actual error-ratio limit.
- Scalar BFGS here is the full algorithm in dimension one, with no assumed update certificate. All denominators used in the run are nonzero. Unit steps pass standard line-search tests.
- The source's unrestricted smooth-convex clause is addressed under ordinary C-infinity smoothness. No positive Hessian or global gradient Lipschitz condition is asserted. The separate stochastic claim is not addressed.
- Built-in LaTeX compilation encountered the known platform-directory error. Existing Tectonic compiled the PDF; two overfull text lines were repaired and the final PDF recompiled. Both final pages were rendered and visually checked without clipping. PDF size: 43488 bytes.
