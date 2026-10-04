# Counterexample to 00000008236

The conjecture's asserted first exact price-of-anarchy value 4/3 is false. Two atomic players each choose one of two resources, both with constant latency 1. All four profiles are Nash equilibria with social cost 2, the actual optimum is 2, and the full worst-equilibrium ratio is 1.

The formal proof additionally treats arbitrary nonempty finite player/resource types and every positive constant-latency vector. Each Nash equilibrium minimizes every player's separable cost, hence attains the global optimum. The exact ratio set is {1}, as is the spectrum over this whole constant-cost class; its sharp supremum is 1. Thus this is also a class-level tight bound. In the explicit all-ones game, every probability law on the four profiles has expected social cost 2, covering randomized equilibria as well.

Actual loads, latency costs, unilateral updates, and Nash conditions are defined. The optimum uses sInf over all profiles and PoA uses sSup over all Nash ratios. The exhibited value belongs to a spectrum quantified over actual positive nondecreasing latency functions. The report targets only the first-value clause, not the source's separate smoothness or zeta claims. No exclusion of constant latencies or PoA 1 appears in either source version.

## Reproduce

With Lean 4.19.0, run `lake update`, `lake exe cache get`, then `lake build` in `lean/`. Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. Public Git configuration is included; ignored local dependency junctions are not submitted.

Compile `report.tex` with a LaTeX engine supporting its standard packages. The included PDF was generated with Tectonic. See `VERIFICATION.md` for validation details.
