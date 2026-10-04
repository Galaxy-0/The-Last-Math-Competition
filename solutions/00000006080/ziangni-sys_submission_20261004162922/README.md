# Proof of conjecture 00000006080

Two actual square-activation feedforward networks share hidden layers and differ only in output weight. Their outputs are L₁(x,y)=(x²−1)²+y² and L₂(x,y)=2(x²−1)²+y². All local and global minima occur at (-1,0),(1,0) with value0, while the common strict saddle at(0,0) has Hessian spectra{-4,2} and{-8,2}.

The Lean source constructs affine dense layers, square activation and readout weights; derives the polynomial outputs; proves actual Fréchet derivatives, complete local/global minimum sets, actual second-partial Hessians and full Mathlib spectra. The existential final theorem supplies both networks, genuine strict saddles, equal minima/values and the explicit perturbation.

Run lake build in lean/ using Lean4.19.0. Public Mathlib revision c44e0c8ee63ca166450922a373c7409c5d26b00b and all dependencies are pinned. See report.tex/report.pdf for the full proof and VERIFICATION.md for validation.
