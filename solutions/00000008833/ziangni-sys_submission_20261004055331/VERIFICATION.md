# Verification

Verified 2026-10-04 UTC with Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

- Direct full-source check `lake env lean Main.lean -DwarningAsError=true`: exit zero.
- Fresh local project `lake build`: passed. The default Main target was built from source.
- Six principal audits (`energy_convex`, `fenchel_conjugate`, `prox_exact`, `zero_saddle`, `orbit_bound`, `product_bound_counterexample`) use only propext, Classical.choice and Quot.sound.
- No sorry, admit, custom axiom declaration or native_decide occurs in the proof source. No auxiliary numerical evidence is required.
- The real Hilbert line, bounded continuous linear map, all-variable adjoint identity, ConvexOn and Continuous properties, genuine sSup Fenchel conjugate, complete global-minimizer predicate, exact proximal update and actual function iterates are verified.
- The proximal characterization includes existence and uniqueness. The Fenchel supremum is bounded above by the proved value and has a proved attaining argument. Saddle inequalities quantify over all real points.
- The contraction and geometric bound cover every initial triple and every natural iteration count. Convergence is in the standard product topology. The ordinary CP initialization xbar=x is a special case; no favorable initial state is assumed.
- Tectonic compiled the actual final two-page PDF without box warnings. Both complete pages were rendered at 1500 pixels and visually inspected: legible text and mathematics, clean margins, no clipping, overlaps or missing glyphs.
- Saved-source editor opened and built-in compiler attempted; its existing environment error was `Unable to find standard directories for platform`. The delivered PDF was compiled successfully with Tectonic.
- Public Git dependency pins retained; local cache junctions and build products ignored. No shared cache writes or lake clean were used. Scoped Git whitespace checks passed.

## Exact source and scope

English: Definition: Chambolle-Pock primal-dual splitting. Conjecture: The convergence domain of CP always requires the two step-size product at most one; acceleration is by diagonal preconditioning with condition-number improvement exactly the ratio of preconditioner spectral radii. (CP step-product preconditioned acceleration)

中文：定义：Chambolle–Pock 原始对偶分裂。猜想：CP 的收敛域恒为两步长积不超过一；加速由对角预条件实现且条件数改善恰为预条件谱半径之比。（CP 步长积预条件加速）

Both originals were read. Neither normalizes the nonzero coupling operator. The example uses standard theta=1 extrapolation, proper continuous convex quadratic objectives and an actual saddle. It disproves the stated universal necessary product bound, while satisfying the familiar operator-dependent sufficient condition. The separate preconditioning clause is not needed for the disproof.

Algorithm correspondence was checked against Algorithm 1 and Theorem 1 of Chambolle–Pock's author preprint, https://www.cmap.polytechnique.fr/preprint/repository/685.pdf. The mathematical convergence proof here is direct and does not assume that theorem.

## Eligibility

Correct upstream: The-Last-Math-Competition/The-Last-Math-Competition. Successful all-state inventory with limit 1000 and complete titles/bodies returned 409 records. Local exact-ID and short-ID checks found no matching PR. Successful direct all-state search for 00000008833 returned an empty list. Metadata marks proven=false and disproven=false; the upstream HEAD solution tree for this ID was empty. Current claims were checked and root approved/reserved this candidate. Inventory retained in work/overnight/43-scratch/all-prs.json. Failed commands were not interpreted as empty results.
