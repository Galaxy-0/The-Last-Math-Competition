# Proof of conjecture 00000007389

This proves standard root-Newton affine covariance on arbitrary real or complex normed spaces. The actual Frechet derivative transforms by the chain rule, its inverse transports the Newton correction, and all defined Newton iterates commute with an invertible affine coordinate change. Identity and composition laws describe the induced tangent-space algebra.

The source's vague algebra phrase is interpreted explicitly in report.tex; no unspecified geometric invariant is claimed. Invertibility of the derivative is exactly the condition for the ordinary Newton step to exist. No finite-dimensional or convergence restriction is imposed.

## Reproduce

Install Lean 4.19.0, enter lean/, then run:

    lake update
    lake build

Mathlib is publicly pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Main.lean prints eight final theorem axiom audits. report.tex is a standalone LaTeX document; its compiled two-page report.pdf is included.
