# Conjecture 00000008550: 4 congruences versus3 kernel ideals

The actual bounded chain C3 has4 lattice congruences but only3 kernel ideals. Distinct congruences given by the identity quotient and the upper-threshold quotient C3→C2 both have zero kernel {0}. All3 ideals are actual zero kernels of bounded-lattice quotient homomorphisms. This defeats both the natural kernel correspondence and any abstract bijection. The separate tower-height clause is not addressed.

Files: report.tex and report.pdf; reproducible lean/ project; verify.py exhaustive independent check; verification/ logs and source. Build with Lean4.19.0: `cd lean`, `lake build`, then `lake env lean -DwarningAsError=true Main.lean`. The public project pins Mathlib v4.19.0; ignored cache junctions are not required for reproduction. Run `python verify.py`; compile with `tectonic report.tex`.

Main.lean defines actual Boolean binary relations on Fin3 and the complete equivalence/meet/join congruence laws, genuine bounded-lattice surjections and their actual kernel relations, actual zero classes and actual ideal closure conditions. Ordinary kernel-checked decide covers all512 relations and8 subsets. Actual counts4 and3 prove no bijection exists. No assumed scalar count data, extra axioms, admitted proofs or native decision shortcuts are used.

C3 is a standard finite example also used in our distinct submission08557 about congruence atoms. This submission independently addresses the kernel-ideal correspondence and fully checks every object needed for that claim; no external submission proof is copied.
