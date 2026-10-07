# Disproof of conjecture 00000003480 (continuous-spectrum assertion for finite graphs)

The conjecture claims that the difference between the fractional chromatic number and the fractional Hall bound takes **every real value** from 0 to 1, with realizations by a Mycielski-type graph family. For finite simple graphs, this is impossible by cardinality, regardless of the formulas for those two invariants.

There are only finitely many simple graphs on each fixed finite labeled vertex set, hence only countably many finite simple graphs in total. The image of this class under any real-valued graph invariant, including a difference of two invariants, is countable. The interval `[0,1]` is uncountable.

The Lean proof represents all finite simple graphs by `Σ n : ℕ, SimpleGraph (Fin n)`, proves that type countable, constructs an injection from `ℝ` into `[0,1]`, and rules out full interval coverage for **arbitrary** real-valued functions on those graphs. In particular, it applies to the two named fractional graph invariants wherever they are defined on finite simple graphs. Their exact LP definitions are not needed for this obstruction.

## Scope

This refutes the stated continuous-spectrum assertion for finite unweighted simple graphs, the setting of the described Mycielski family. If the intended claim allows continuously weighted or otherwise uncountably parametrized objects, that would be a different statement and this argument would not decide it. The endpoint-one clause is not analyzed.

## Reproduce

From `lean/`, run `lake build`. `#print axioms no_full_interval_of_difference` appears at the end of `Main.lean`.
