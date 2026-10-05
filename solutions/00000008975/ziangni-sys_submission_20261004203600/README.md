# Disproof of conjecture 00000008975

The normalized primitive non-scalar polynomial matrix K(u)=diag(1,1+u^3) solves the boundary reflection equation for the actual invertible tensor flip R=P. Its degree is three, violating the stated degree/order bound of two.

The Lean source verifies actual Kronecker tensor lifts, flip conjugation, the all-parameter reflection equation, genuine eight-dimensional Yang-Baxter matrix identity and tensor-leg bridge, polynomial evaluation, exact degree, normalization, invertibility except at -1, absence of any common nonunit polynomial factor and failure of scalarity.

Read report.pdf or report.tex. Reproduce by running lake build inside lean/ with Lean 4.19.0 and the publicly pinned Mathlib dependency.

The counterexample targets the source's unqualified polynomial degree clause. It does not address the undefined G/H family count or a different classification restricted to a specified nonconstant R-matrix.
