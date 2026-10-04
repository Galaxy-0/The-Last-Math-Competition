# Authoring-agent adversarial review: 00000003961

This is the authoring agent's self-review. A parent review is required separately before publication; no external independent review is claimed.

## Claim correspondence

The source explicitly defines Johnson vertices as k-element subsets and adjacency by symmetric difference of size 2. It asserts cutoff for every `k <= N/2` without a requirement that `k` grow. The sequence `k = 1`, `N >= 5` is therefore legal. Cutoff is an asymptotic property of a sequence of chains; a counterexample must be a complete sequence, not merely one finite graph. This package provides the entire increasing-size sequence and proves its ratio identically 2.

The standard half-lazy convention is stated explicitly. The argument refutes the cutoff clause itself and does not infer failure from an unspecified cutoff-time constant. It does not claim that all other parameter regimes lack cutoff.

## Mathematical and implementation attack checks

- The Johnson graph is built on actual singleton finite subsets using its given symmetric-difference condition. The label map is proved bijective, and adjacency under that map is proved equivalent to distinct labels.
- The neighbor count is derived from the actual graph predicate. The transition matrix is matched to the graph and reciprocal neighbor count, so it is not merely a matrix chosen to have the desired spectrum.
- Every transition probability is strictly positive. The construction is a connected, aperiodic, nontrivial family; disconnection and periodicity do not explain the failure of cutoff.
- The matrix is actually doubly stochastic, and all powers remain so. The uniform mass function sums to one and is stationary.
- The matrix-power identity follows by multiplication and induction, using the idempotence of the actual uniform matrix. It is not an axiom or an assumed spectral formula.
- Total variation is the actual finite sum of absolute differences divided by two. The exact value is derived separately for diagonal and off-diagonal entries and is the same for every initial state.
- The worst-initial-state bound is represented by universal quantification over starting states. This is equivalent to the maximum formulation for this finite state space, without assuming a chosen initial state is worst.
- Mixing times are genuine minima: at tolerance 1/4, times 0 and 1 fail and time 2 succeeds; at tolerance 3/4, time 0 fails and time 1 succeeds. They are not merely upper bounds.
- The distances tend to zero and a mixing time exists for every positive tolerance. The infimum of an empty set cannot cause the displayed values.
- The cutoff ratio is constant 2 for all indices, and Lean uses uniqueness of real limits to show it cannot tend to 1.
- The chosen primary reference supplies the standard cutoff definition. The complete-graph calculation is self-contained and is not claimed as new mathematics.
- Exact Python checks reconstruct actual subset graphs and multiply rational matrices. Their finite sample does not substitute for the general Lean proof.

## Evidence gate

Fresh build and direct Lean must pass with warnings treated as errors, and all printed theorem dependencies must be among `propext`, `Classical.choice`, and `Quot.sound`. The raw bilingual source must match `SOURCE.md` byte for byte. Final TeX/PDF/source hashes and all-page visual checks are recorded in `BUILD.json`. The native compiler's platform failure must be recorded separately from the actual Tectonic PDF export.

Parent review and final upstream duplicate/source checks remain separate requirements before publication.

## Completed checks at handoff

- Fresh `lake build` and direct Lean with `-DwarningAsError=true`: passed.
- All 16 printed theorem-axiom audits: only the standard foundational axioms listed above; one graph-bijection theorem needs just `propext` and `Quot.sound`.
- `verify.py`: passed every graph, matrix, stationary-distribution, total-variation, and minimum-time check for all five sizes and six times.
- The raw source and `SOURCE.md` have identical bytes and SHA-256 `4b57f16a4f052d983f6d1de29562b8143ed0b38b2d6eb9228005840b5a094225`.
- The final Tectonic export has two pages and no warnings. Both final 1500-pixel Poppler renders were opened and checked for readable mathematics, intact margins, no overlaps, and consistent pagination.
- Final Lean, TeX, and PDF hashes match `BUILD.json`. The native compiler's actual platform failure is recorded separately from the successful Tectonic build.
