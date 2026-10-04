# Disproof of conjecture 00000008254

The actual symmetric zero-payoff 2×2 game has no evolutionarily stable strategy. Every resident probability vector has a distinct feasible pure mutant, and all actual bilinear expected payoffs are zero. The strict small-invasion fitness comparison fails for an explicit feasible positive invasion proportion below every proposed threshold.

The proof covers all strategies, including boundary and interior vectors. The source asserts existence for all 2×2 games without a nondegeneracy assumption. The direct invasion argument does not depend on an unproved ESS characterization; the conventional payoff test is separately refuted.

report.tex and report.pdf contain the complete proof and correspondence. lean/Main.lean defines the actual symmetric game, probability simplex, pure mutants, expected payoff, population mixture with validity, the quantified invasion condition and its universal failure. verification/ preserves the source and checks.

From lean/, with Lean 4.19.0, run:

```text
lake update
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
```

Mathlib is publicly Git-pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b; ignored local cache junctions are not submitted. No auxiliary computation is needed, and no admitted proofs, custom axioms or native decision procedures are used.

The saved LaTeX source is opened in the built-in editor/compiler. Its existing platform-directory error is handled by Tectonic compilation of the delivered PDF, followed by rendering and inspection of every final page.
