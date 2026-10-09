# Proof of 00000005130

For the identical system I x = e1 and starting point x0 = 0, take SPD preconditioners M1 = diag(1,2) and M2 = diag(2,1). Their spectra, preconditioned-system spectra and Richardson iteration spectra agree exactly. Nevertheless M1 terminates in one step, whereas M2 has error 2^(-k) e1. A quarter-turn conjugates the preconditioners and realizes the full trajectory relation through the rotated initial error.

This establishes the source's complete existential claim using genuine preconditioned Richardson iteration. No universal claim about all iterative methods or initial directions is made.

Run `lake build` in `lean/` with Lean 4.19.0 and the pinned public dependencies. See `report.pdf` and `report.tex` for the full proof.
