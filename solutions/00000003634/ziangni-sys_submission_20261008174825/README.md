# Conjecture 00000003634: disproof

The constant, hence one-periodic, systems x'=0 and x'=Nx with N(u,v)=(v,0) have all Floquet exponents zero. The first is Lyapunov stable and the second is unstable, because its solutions grow as (u+tv,v). This disproves determination of stability by real-part signs alone. A Jordan-block condition is necessary on the zero-real-part boundary.

## Formal scope

The project uses actual continuous linear operators on ℝ × ℝ. It proves N²=0 and exp(tN)=I+tN from the operator exponential series, verifies the inverse and differential equation, and proves the two constant coefficient functions are one-periodic. The chosen genuine Floquet decomposition has periodic factor I and exponent matrix equal to the coefficient operator. The code proves directly over ℂ that every nonzero complex eigenvector for either exponent matrix has eigenvalue zero, with a nonzero witness for eigenvalue zero. Lyapunov stability is defined with the full ε,δ,initial-vector,time quantifiers; the zero flow is stable and the nilpotent flow violates ε=1 for every δ>0.

No flow, exponential or eigenvalue certificate is assumed. The report discusses monodromy multipliers and the boundary Jordan obstruction. The stability notion is ordinary Lyapunov stability, not asymptotic or exponential stability.

## Reproduction and validation

Use Lean 4.19.0 and pinned Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b, as specified in the public lakefile and manifest. Run `cd lean`, `lake update` if dependencies are absent, and `lake build`. Local ignored `.lake` cache junctions are not submitted. One final full build succeeded and all six final printed audits reported only propext, Classical.choice, Quot.sound. Harmless tactic-linter warnings concern redundant patterns/tactics; no admissions, custom axioms, native decision or unsafe code occur.

Compile `solution.tex` with Tectonic or a standard LaTeX engine. The final one-page PDF compiled, rendered with Poppler and was visually inspected without clipping or overlap. No auxiliary computations are required.
