# Verification

Verified 2026-10-04 UTC with Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

- Fresh project `lake build`: success, 2217 targets, Main built from source.
- Direct `lake env lean Main.lean -DwarningAsError=true`: exit 0.
- Five audits (`maximum_orbit`, `raw_probability`, `gibbs_mass`, `weak_limit_minimum`, `not_weak_limit_maximum`) use only `[propext, Classical.choice, Quot.sound]`.
- Source scan: no `sorry`, `admit`, `native_decide` or custom axiom declarations.
- Actual objects include the finite compact Borel space, continuous map and observable, all-state maximizer set, all iterates on the maximum orbit, exponential partition function, normalized Dirac combinations, probability measures, Bochner integrals and the standard weak probability-measure topology.
- Every state's Gibbs mass is proved from the definitions. Convergence is tested against every bounded continuous real function and uses the positive right-hand neighborhood filter. The two actual Dirac measures are distinguished on a measurable singleton. No scalar probability table or custom weak-convergence relation is assumed.
- Native source editor opened and compilation attempted; platform error: `Unable to find standard directories for platform`. Actual Tectonic compilation succeeded without TeX box warnings.
- Both final PDF pages rendered at 1500 pixels with Poppler and visually inspected in full: clean margins and legible formulas, no clipping, overlap or missing glyphs.
- Scoped Git whitespace checks passed. Public dependency pins are retained; local caches and junctions are ignored. No lake clean was used.

## Source scope and eligibility

Both English and Chinese originals explicitly specify mu_t proportional to exp(-f/t) and state that when the maximum set of f is a periodic orbit, the limit is unique and equals the equidistribution on that orbit. The example retains that negative sign, uses equal positive reference weights, and has an entire maximum set which is a period-one orbit. It disproves this clause of the conjunction; no claim about the additional equilibrium, oscillation or pressure assertions is needed.

Counting reference measure and uniform reference probability yield the same normalized family. The mathematical and formal limits are taken only as t approaches zero through positive temperatures. The finite discrete space is Hausdorff, so distinct limiting Dirac measures cannot both be weak limits.

Eligibility used exact upstream `The-Last-Math-Competition/The-Last-Math-Competition`. A successful complete all-state title/body inventory with limit 1000 and local exact 11-digit and short-ID checks found no prior matching PR. Successful direct all-state search returned no matches, metadata marked the conjecture unsolved, and the upstream tree had no solution path. The inventory is retained in `work/overnight/40-scratch/all-prs.json`. Root approved and reserved the candidate.
