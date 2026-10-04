# Disproof of the strict sampling improvement in 00000008776

The actual consistent overdetermined system A=(1,1)^T,b=0 has identical nonzero rows. Its true mean least-squares objective is x^2/2 with unique minimizer zero, and its mean-Gram diagonal inverse is1. At all nonzero states, the residual-proportional optimal law is uniform. Every row SGD update with step1/2 is x/2, hence the two algorithms have identical full laws and actual expected errors2^-k from start1. There is no strict improvement. The source excludes neither identical rows nor equality cases.

The first clause may describe a sharp worst-case Kaczmarz bound and is unused; the block-size and harmonic-ratio assertions are also unused. The report does not deny improvements on other systems or a possible non-strict comparison.

Lean defines the matrix, actual losses/gradients/preconditioner, normalized residual scores, actual row PMFs and genuine bind-generated SGD laws, and computes the full laws, actual Bochner expected errors and convergence. Actual finite iterates remain positive, so no zero-residual convention affects this run.

Reproduce in lean/ with Lean4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Build prints standard theorem axiom audits. No admitted proofs, custom axioms or native decision procedures are used.

The complete report is disproof.tex/disproof.pdf. Native compilation returned the known platform-directory failure. Existing Tectonic compiled the two-page PDF; both rendered pages were visually inspected without clipping or overflow.
