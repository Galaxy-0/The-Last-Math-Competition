# Conjecture 00000008839: the proposed Yosida error formula fails

On the real Hilbert space take the actual continuous linear map A=4 id and lambda=1/4. The actual resolvent is (1/2)id, the standard Yosida approximation is 2 id, and the actual error norm is2, exceeding lambda times the actual operator norm4, whose product is1. Equality and even an upper-bound reading both fail; the pointwise unit-vector error also equals2. The operator is proven maximal monotone. The separate approximate-solution convergence clause is not addressed.

Files: complete report.tex and report.pdf, reproducible lean/ project, verification/ evidence. No numerical auxiliary code is needed.

Using Lean4.19.0, run `cd lean` then `lake build`; check the whole source/audits with `lake env lean -DwarningAsError=true Main.lean`. The public configuration pins Mathlib v4.19.0. Ignored local cache junctions are not required for reproduction. Compile the PDF with `tectonic report.tex`.

Main.lean constructs actual CLMs, proves both resolvent inverse identities, actual approximation/error identities and actual operator norms, verifies the pointwise unit error, and proves monotonicity/maximality by actual graph extensions. The final theorem packages a valid counterexample to the bound, hence also to the stated equality. No norm or resolvent scalar data are assumed. The report's general a-id formula is explanatory only; the complete concrete example is formalized.
