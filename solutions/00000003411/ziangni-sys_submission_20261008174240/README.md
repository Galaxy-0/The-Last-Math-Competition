# Conjecture 00000003411: disproof

Stationary two-state Markov chains with identical rows (p,1-p) have entropy rate H(p) = -p log p -(1-p) log(1-p). Their maximum-entry transition distance is exactly |p-q|. At q=0, every proposed global Lipschitz constant C is violated by p=exp(-(C+1)). The conjecture gives no uniform positive lower bound on probabilities.

## Reproduction and scope

Run `cd lean` and `lake build`; if dependencies are absent, first run `lake update`. Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` are publicly pinned. The ignored `.lake` local cache junctions are not required for reproduction and are not submitted.

`Main.lean` defines actual two-state transition kernels and stationary distributions, verifies nonnegativity, row sums and stationarity, and evaluates the usual stationary finite-state entropy-rate finite sum. It proves the exact transition-matrix distance identity using the function-space maximum metric. The final theorem disproves a global Lipschitz bound already on this family; no scalar replacement or assumed entropy/distance certificate is used. The real logarithm's totalized value at zero gives the standard convention 0 log 0 = 0.

Compile `solution.tex` with Tectonic or a standard LaTeX distribution. No auxiliary computation is needed.

## Validation

One final full `lake build` succeeded. All five printed final theorem audits use exactly `propext`, `Classical.choice`, and `Quot.sound`; no admissions, custom axioms, native decision or unsafe code occur. The two-page PDF compiled with Tectonic, rendered with Poppler, and both pages were visually inspected with no clipping or overlap.
