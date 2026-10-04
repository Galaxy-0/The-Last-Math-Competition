# Solution Review — Conjecture 00000009761 (PR 456)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004120908`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the official statement proposes the universal trace-class inequality \( |\lambda_n|\le((\prod_{k\le n}s_k)^{1/n}+s_n)/2 \), then claims optimality, second-order diagonal attainment, and uniqueness of coefficients. No normality/self-adjointness restriction is stated.
- Change scope: only the allowed submission directory is added. Base metadata marks the conjecture unsolved and no prior solution existed.
- LaTeX: rebuilt from a fresh copied tree with `latexmk -pdf -interaction=nonstopmode -halt-on-error` (exit 0; two pages; no errors or unresolved warnings). Shipped and fresh PDFs have the same mathematical text up to Tectonic/pdfTeX ligature and hyphenation extraction artifacts (0.9962 normalized similarity; 0.99973 with whitespace removed). Both shipped pages were split and rasterized successfully.
- Lean build: Lean 4.19.0 / Lake 5.0.0, Mathlib exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`; exact-revision official package artifacts were preseeded, the project's Main target compiled independently, and `lake build` exited 0 (`[2105/2106] Built Main`). `lake env lean -DwarningAsError=true Main.lean` also exited 0. All eight audited theorems depend only on `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; the sole broad grep hit is review prose.
- Auxiliary program: `python3 -X utf8 verify.py` exited 0. Its JSON is semantically identical to the shipped expected output (only CRLF versus LF differs). I also ran a separate exact-`Fraction` recomputation of the Gram matrix, characteristic coefficients, SVD product, and \(3/4<1\); all passed.
## Semantic audit
The witness is a genuine complex \(2\times2\) matrix, \(A=\begin{pmatrix}1&3/2\\0&1\end{pmatrix}\), represented by Mathlib `Matrix (Fin 2) (Fin 2) ℂ` and instantiated as an operator on `EuclideanSpace ℂ (Fin 2)`. The conjugate-transpose/Hilbert-adjoint bridge is proved, and finite-dimensional operators are trace class; the zero extension \((2,1/2,0,\dots)\) is proved nonnegative summable with sum \(5/2\). Thus the example lies in the conjecture's stated domain.

The characteristic polynomial of \(A\) is \((X-1)^2\), and Lean proves the full root multiset \(\{1,1\}\), preserving algebraic multiplicity. The Gram matrix is \(\begin{pmatrix}1&3/2\\3/2&13/4\end{pmatrix}\), with characteristic polynomial \((X-4)(X-\tfrac14)\). Independently, Lean proves actual unitary matrices \(U,V\) and the exact SVD \(A=U\operatorname{diag}(2,\tfrac12)V^*\), with nonnegative decreasing diagonal entries. Therefore \(s_1=2,s_2=\tfrac12\) are genuinely the ordered singular values, not assumed numerical data.

At \(n=2\), \(\lambda_1=\lambda_2=1\), while \((\sqrt{s_1s_2}+s_2)/2=(1+\tfrac12)/2=\tfrac34\). Lean proves \(\|eigenvalues\ 1\|=1\not\le3/4\). The definition `ArithmeticStrengtheningInDimensionTwo` quantifies over all \(2\times2\) matrices and all complete ordered eigenvalue/SVD spectral data; any universal trace-class version of the stated inequality implies this finite-dimensional case. Its negation is proved from the constructed witness, so the witness is non-vacuous. Disproving the inequality also invalidates its claimed universal optimality and coefficient uniqueness. The report is honest that classical product Weyl bounds still hold and no normal-operator variant is addressed.
## Issues found
none blocking
## Verdict rationale
The exact nonnormal \(2\times2\) counterexample is mathematically correct, belongs to the conjecture's trace-class domain, and is certified through both characteristic polynomials and a complete unitary SVD. The Lean theorem corresponds faithfully to the official \(n=2\) inequality, all builds and auxiliary checks pass, and only standard foundational axioms are used.

## Disposition
APPROVED — ready to merge (PR 456). Independent fresh rebuild, direct warning-as-error Lean check, axiom audit, exact auxiliary recomputation, PDF rebuild/comparison, source inspection, forbidden-pattern scan, and semantic audit all passed.
