# Conjecture 00000002506: proof

The Tucker contraction of an actual finite coordinate core with one rectangular factor matrix per mode remains a Tucker contraction after arbitrary further mode products. The updated factors are the actual matrix products. This proves the full stated algebraic factorization and closure property for arbitrary finite arity and varying finite index sets, over every commutative semiring, including real and complex scalars.

## Formal scope

Lean uses genuine dependent coordinate arrays, finite contractions and rectangular matrices. It proves contraction composition, the identity kernel and identity-core factorization, universal Tucker existence, closure of every given core/factor representation, same-mode matrix composition and distinct-mode commutation. No factorization or contraction certificate is assumed. Finite sets may be empty, including the mode set. Decidable equality instances on finite types are routine choices. No smallest-core, orthogonal-factor or optimal-rank claim is made, since the source states none.

## Reproduction and validation

Use Lean 4.19.0 and publicly pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. From lean/, run lake update if dependencies are absent and lake build. Ignored local .lake junctions are not submitted. Compile solution.tex with Tectonic or a standard LaTeX engine. No auxiliary computation is needed.

One final successful full lake build after draft fixes printed seven final audits, all using only propext, Classical.choice and Quot.sound. Only unused section-variable warnings occur. No incomplete proof, custom axiom, native decision or unsafe code occurs. The one-page PDF compiled without layout warnings, rendered with Poppler and passed visual inspection without clipping or overlap.
