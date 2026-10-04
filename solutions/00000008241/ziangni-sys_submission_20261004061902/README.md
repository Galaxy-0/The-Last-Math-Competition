# Disproof of conjecture 00000008241

The coalition-gain bound fails in an actual two-agent, one-good VCG auction. True values (2,1) yield utilities (1,0). Every unilateral admissible report has gain at most zero, with maximum zero attained. Coalition reports (2,0) yield utilities (2,0), giving total coalition gain one, strictly exceeding twice the maximum single-agent gain zero.

The actual allocation maximizes reported welfare over all three feasible outcomes including leaving the good unallocated. Payments are defined by Clarke externalities, and the best other-agent welfare is proved to be an attained maximum. The formalization quantifies over every nonnegative unilateral bid and handles all ties.

This refutes the first clause of the conjunctive source; it does not separately analyze the revenue-minimality and uniqueness clauses. Coalition gain means total true-valuation utility change, not auctioneer revenue loss.

See report.tex and the complete two-page report.pdf. From lean/, run:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b are pinned by the public project configuration. Ignored local dependency junctions used for validation are not submission materials.
