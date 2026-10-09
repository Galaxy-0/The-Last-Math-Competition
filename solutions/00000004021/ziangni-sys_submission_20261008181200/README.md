# Conjecture 00000004021: disproof

Initial evaluation is a genuine 1-Lipschitz functional on continuous real paths with the supremum metric. The smooth constant paths at0 and1 have identical ordinary iterated-integral signatures, so every finite signature linear functional has worst-case error at least1/2 on this compact two-path family. Thus no fixed finite C gives the proposed C/sqrt(N) rate. On all constant paths no finite uniform bound exists at all.

## Formal scope

Path is the actual ContinuousMap space on Icc0 1, and initial evaluation is proved Lipschitz using its actual supremum metric. The one-dimensional smooth signature is defined recursively by interval integrals against the actual derivative. All constant paths have zeroth level1 and positive levels0. Lean verifies equality of every finite signature linear functional, the two-path error lower bound, the stronger unbounded-family obstruction, and failure of the proposed rate for every nonnegative C.

The source imposes no common starting point or translation invariance of target functionals. Ordinary signatures discard initial position. A common-start or augmented-signature assertion would be a different statement. Including the zeroth level makes the counterexample cover affine combinations as well.

## Reproduction and validation

Use Lean4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b as pinned in the public lakefile/manifest. From lean/, run lake update if needed and lake build. Ignored local .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine.

One final full lake build succeeded without warnings. All six final printed axiom audits use exactly propext, Classical.choice, Quot.sound. No incomplete proof, custom axiom, native decision or unsafe code occurs. The one-page PDF compiled without layout warnings, rendered with Poppler and passed visual inspection with no clipping or overlap. No auxiliary computation is needed.
