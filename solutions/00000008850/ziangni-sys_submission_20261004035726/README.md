# Conjecture 00000008850: single-valued continuity does not force strong monotonicity

A(x)={0} on the real Hilbert space is maximal monotone and not strongly monotone. On the connected domain R×(0,infinity), the actual variational inclusion has the unique solution p/lambda, jointly continuous in both parameters. This disproves the necessary direction of the explicitly stated equivalence in both source languages. Other conjecture clauses are not addressed.

Contents: report.tex and compiled report.pdf, reproducible lean/ project, verification/ evidence. No numerical auxiliary code is needed.

With Lean4.19.0, run `cd lean` and `lake build`, then `lake env lean -DwarningAsError=true Main.lean` to check the whole source and axiom audits. The public project pins Mathlib v4.19.0. Ignored cache junctions used locally are unnecessary for reproduction. Compile the PDF using `tectonic report.tex`.

Main.lean uses actual real topology and algebra. Solution means existence of u in A(x) with u+lambda*x-p=0, not an asserted scalar formula. Single-valued continuity means a continuous function whose graph equals the full solution relation on the parameter domain. Maximality is proved for actual monotone graph extensions. Final theorem negates the universal equivalence even with the customary maximal-monotonicity and positive-lambda restrictions.
