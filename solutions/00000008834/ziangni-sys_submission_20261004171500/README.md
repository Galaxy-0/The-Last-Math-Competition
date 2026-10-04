# Disproof of conjecture 00000008834

On the real Hilbert line, the actual maximal monotone operator A(x)={1} has no zero. Every positive Tikhonov regularization has the unique root -1/e. With e(t)=1/(t+1), these roots form a divergent path. The actual regularized flow u(t)=-(t+1)/2 solves u'+A(u)+e(t)u contains zero and also fails both norm and weak convergence. Both source versions omit a zero-existence assumption; the rate clause is unused.

Lean verifies the actual graph and maximality against every monotone extension, all positive regularized roots, the positive vanishing parameter, the flow derivative and differential inclusion, and genuine nonconvergence of both real-time paths.

From lean/, with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The full build prints final theorem axiom audits. No admitted proofs, custom axioms or native decision procedures are used.

The complete report is disproof.tex and disproof.pdf. Native compilation returned the known platform-directory failure; existing Tectonic successfully compiled the one-page PDF. Its full rendered page was visually checked without clipping or overflow.
