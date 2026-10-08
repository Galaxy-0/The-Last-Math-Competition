# Conjecture 00000007863: full-budget query counterexample

This packet refutes the source's necessary unrestricted-budget positive linear query lower bound. For k=n, one uniform algorithm returns the entire actual ground set without an oracle call. It is exactly optimal for every normalized monotone submodular objective, so its worst-case expected query count is zero. The unbounded family n=k contradicts every eventual positive c*n universal lower comparison.

`FullBudgetOracle.full_budget_counterexample` is premise-free. It combines actual ground-set cardinality, a nontrivial cardinality objective, the exact positive approximation ratio, a normalized singleton seed law, all-objective feasibility and actual greatest-value optimality, typed oracle interpreter output/cost, expected zero cost and the asymptotic contradiction.

`lean/Main.lean` retains actual objectives on Finsets(Fin n), with f(empty)=0, subset monotonicity and the standard union/intersection submodular inequality. `ValueProgram` and `run` model actual return and value-query nodes; the continuation receives the real oracle answer and each query adds one to the interpreted cost. `expectedQueries` is a finite weighted sum under an actual normalized singleton seed law. The protocol subclass provides an allowed witness against a broader randomized lower bound; it is not a replacement definition of the full optimal randomized query complexity.

The source states no k<n exclusion or fixed-k-only asymptotic. We use the standard feasible-set approximation output, without adding a requirement to report its unknown objective value. These scope conventions are disclosed for independent source-bound review. The improved-approximation jump, greedy-query upper bound, exact exponent and information-theoretic explanation are not separately settled; refuting a necessary conjunct does not prove every remaining clause false.

The exact bilingual source is retained in `original.md` and `00000007863.md`; `source-correspondence.md` maps its properties, scope and conclusions. `proof.tex` and the two-page `proof.pdf` give the English argument.

The author directly compiled Main.lean and emitted an owned Main.olean using official Lean 4.33.0 and the locked public mathlib configuration (revision db584cd6d46c92f209a44c0f1c829460d327499d). The parent supplies the private pinned dependency copy and owns `lake build +Main`, fresh kernel replay, deterministic submission gate and independent semantic/PDF acceptance. Nothing in this author packet is locally_verified or an upstream submission.

The root coordinator identified the elementary k=n route; the same-run sealed 7863 scout formalized its core. This package explicitly reuses that proof and adds the full certificate and paper. No first-discovery or new-mathematics claim is made, and no sealed scout or completed 7862 file was modified.
