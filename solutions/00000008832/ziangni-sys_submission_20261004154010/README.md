# Disproof of conjecture 00000008832

On the real Hilbert space, A(x)={0} and B(x)=1 are maximal monotone and their single-valued versions are Lipschitz. The genuine forward-backward-forward stages with half-step give x_next=x-1/2, so every starting trajectory is x0-n/2 with no weak or strong limit. The backward stage solves the unique resolvent equation exactly, and the half-step satisfies the usual strict L=1 bound.

The actual inclusion has no zero. This explicitly identifies the missing existence assumption in the source's unqualified convergence claim, not a failure of the standard theorem with existence assumed. Full report.tex/report.pdf and the pinned Lean project are included.

Run `lake build` in lean/ with Lean4.19.0 and public Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. Local junctions/build products are ignored.
