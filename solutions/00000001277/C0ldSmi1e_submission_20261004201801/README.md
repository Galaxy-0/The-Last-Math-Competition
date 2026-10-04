# Disproof of conjecture 00000001277

On three states, forbid self transitions and give each of the other two successors probability one half. With the uniform initial law this is a stationary, genuinely dependent first-order Markov chain. Its entropy rate is `log 2`, the largest possible value under these constraints, while its transition support has two entries in every row and column. It is not a partial permutation.

The comparison includes every initial distribution and every admissible transition kernel on the same three states; competitors need not be stationary. Moreover, every partial-permutation-support kernel has entropy rate zero for every initial distribution, so no such kernel can be an optimizer. This refutes the support clause, and hence the conjunction in both source languages. We do not claim a separate disproof of an unspecified permutation-block formula.

## Contents

- `conjecture.md`: byte-for-byte copy of the exact bilingual source.
- `main.tex` and `main.pdf`: complete mathematical disproof.
- `lean/`: Lean 4.19.0 / Mathlib v4.19.0 project with all dependency revisions pinned.
- `VERIFICATION.md` and `verification/`: execution records and exact file hashes.
- `SEMANTIC_REVIEW.md`: independent mathematical and statement-fidelity review.

## Reproduce

From the submission's `lean` directory, using the pinned toolchain:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture1277/Entropy.lean
lake env lean -DwarningAsError=true Conjecture1277/Words.lean
lake env lean -DwarningAsError=true Conjecture1277/Markov.lean
lake env lean -DwarningAsError=true Conjecture1277/Counterexample.lean
lake env lean -DwarningAsError=true Conjecture1277.lean
lake env lean -DwarningAsError=true Check.lean
```

The default library target imports every proof module. `Check.lean` prints all 16 definitions, checks all 56 theorem types and the named finite-history `Fintype` instance, and prints the corresponding 57 axiom dependencies. The report uses standard LaTeX packages and its matching PDF is exported with Tectonic 0.17.0. No numerical or simulation-based result is used; there is no auxiliary mathematical computation to reproduce.

## Formal correspondence

`Entropy.lean` defines Shannon entropy as the finite sum of `Real.negMulLog` of actual PMF masses. It proves the joint-law chain rule from actual `PMF.bind` and `PMF.map` probabilities, including zero-probability cases, and proves invariance under relabeling outcomes.

`Words.lean` stores a history of `n+1` states by successive appending and gives an explicit equivalence with ordinary tuples `Fin (n+1) → α`. `Markov.lean` constructs actual probability mass functions for those histories. It proves prefix consistency, the transition-product identity, and the conditional next-state probability for each positive-probability history. The corresponding tuple laws have the same entropy. This coherent finite-dimensional representation is sufficient to define the chain's block entropies; no separately constructed infinite-path-space measure is claimed.

`HasEntropyRate` is the actual limit of normalized block entropies, not an assigned row functional. For a stationary initial law the project derives the familiar weighted-row formula. More generally, without stationarity, a row entropy bound `c` gives `H(X₀,…,Xₙ) ≤ H(X₀)+n c`; constant row entropy gives equality and a true rate limit equal to `c`.

`Counterexample.lean` constructs the uniform initial law and the off-diagonal one-half transition kernel, proves invariance of the initial law, and exhibits dependence of the first two states. Each admissible row is a binary distribution, so its entropy is at most `log 2`. A partial permutation support has at most one positive entry per row and column; row stochasticity then forces every row to be a point mass, with entropy zero.

The main module proves the witness block entropy `log 3+n log 2`, its maximizing entropy rate, the universal admissible block bound, and the zero rate of every partial-permutation kernel. `explicit_counterexample` collects the witness, while `no_partialPermutation_maximizer` excludes even the weaker interpretation that some optimizer has partial-permutation support. `conjecture_1277` negates the support assertion for this valid first-order constraint matrix. Since `k=1` is an allowed instance, this suffices to disprove the universal conjecture.

All logarithms are natural; changing the logarithm base rescales all rates by the same positive constant. The report cites [Han et al., arXiv:1802.07889](https://arxiv.org/abs/1802.07889) only for standard entropy-rate terminology. The required identities are proved in Lean rather than assumed from that reference.

These are local validation and internal review results. Maintainer acceptance remains a separate decision.
