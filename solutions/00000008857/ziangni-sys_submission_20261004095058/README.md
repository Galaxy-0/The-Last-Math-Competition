# Disproof of conjecture 00000008857

Two players choose arbitrary real actions and minimize costs c_i(x)=exp(x_i). Their actual pseudogradient is monotone, costs are smooth, positive and strictly convex in each player's action, but every player can improve at every profile by replacing x_i with x_i−1. Hence the actual Nash equilibrium set is empty.

Both original languages assert universal nonemptiness without a compactness or coercivity assumption. The report explicitly uses unbounded strategy spaces and does not contradict compact-strategy existence theorems. Refuting the nonemptiness conjunct suffices; the other clauses are not claimed false.

The Lean project constructs actual Euclidean profiles, coordinate updates, derivatives, inner-product monotonicity and all-action Nash quantifiers. It also verifies domain geometry, cost positivity, smoothness and unilateral strict convexity.

From lean/, using Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
lake env lean Main.lean -DwarningAsError=true
```

Mathlib is publicly pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Ignored local dependency junctions are build conveniences and are not submitted. See verification/ for the original statement and validation records. The report PDF is compiled from report.tex and all its pages are visually checked.
