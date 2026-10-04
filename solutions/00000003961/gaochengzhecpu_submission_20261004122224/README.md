# Conjecture 00000003961: J(N,1) has no total-variation cutoff

The source says that the lazy walks on Johnson graphs exhibit total-variation cutoff for all `k <= N/2`. The legal sequence `k = 1`, `N -> infinity` is a counterexample. Its vertices are actual singleton subsets, so `J(N,1)` is the complete graph. For the standard half-lazy walk and every `N >= 5`, the exact worst-state total-variation distance is

```text
d_N(t) = ((N - 1) / N) * ((N - 2) / (2 * (N - 1)))^t.
```

Consequently, the minimum mixing times at tolerances `1/4` and `3/4` are exactly `2` and `1`. Their ratio is constantly `2`, and cannot tend to `1` as required by total-variation cutoff. Both language versions of the source allow fixed `k`; this conclusion does not address a modified conjecture requiring `k -> infinity`. The calculation is elementary and is not presented as a new general result about random walks.

## Contents

- `main.tex`, `main.pdf`: complete proof, source interpretation, and correspondence with Lean.
- `SOURCE.md`: exact original bilingual source bytes.
- `lean/Main.lean`: actual Johnson subset graph, labeling bijection, degree, transition matrix, stochasticity, uniform stationarity, exact matrix powers and total variation, minimum mixing times, and cutoff contradiction.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: portable pinned project.
- `verify.py`: independent exact-rational checks using graph construction and matrix multiplication at five finite sizes.
- `verification/BUILD.json`, adjacent logs, and `SELF_REVIEW.md`: actual verification and authoring-agent adversarial review.

## Reproduce

Install Lean through elan. From `lean/`, run:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

Lean is pinned to 4.19.0; Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All transitive dependencies are locked and use public Git URLs. On a fresh machine, `lake exe cache get` may obtain the official dependency cache to avoid recompiling Mathlib.

From the submission directory:

```text
python verify.py
tectonic main.tex
```

The Python cross-check uses only the standard library. It constructs singleton subsets and symmetric-difference edges, forms the half-lazy neighbor transition probabilities, and multiplies rational matrices at sizes `5, 6, 8, 12, 20`. It verifies every row's probability and total-variation formulas at times `0` through `5`. These finite tests supplement the infinite family theorem proved in Lean.

## Formalization correspondence

Lean uses `N = n + 5` to index exactly the sizes under discussion. `Vertex n` consists of actual finite subsets with cardinality one. `singleton_bijective` and `johnson_singleton_adj` justify relabeling them by `Fin (n + 5)`, and `neighbor_count` derives the degree. `transition_from_johnson` and `transition_by_neighbor_count` connect the transition matrix to that graph and its actual number of neighbors. The relabeling changes names of states only.

`transition_doubly_stochastic` and `powers_doubly_stochastic` establish nonnegative entries and row/column sums through Mathlib's existing matrix structure. The uniform mass function has positive total mass one and is proved stationary. `powers_decomposition` proves the matrix identity for every integer time, and `tv_exact` derives the exact finite total-variation sum from the identity. The distance tends to zero, and a finite mixing time exists for every positive tolerance.

`mixingTime` is the infimum of the actual set of integer times at which all starting states satisfy the tolerance. The set is nonempty, and its least elements for the two needed tolerances are proved directly. `HasTotalVariationCutoff` uses the standard real-limit ratio criterion from Hermon and Peres, arXiv:1610.04357. `no_total_variation_cutoff` contradicts that criterion at tolerance `1/4`.

No spectral gap is postulated or approximated. The conjecture's cutoff-time multiplier is not analyzed because the cutoff assertion itself fails. The proof does not require a sample-path probability process: finite transition powers and their probability-mass functions completely define the finite-state mixing distances used in the statement.

## Verification

Actual clean-build commands, exit codes, theorem-axiom dependencies, source hashes, Python output, and PDF rendering are in the verification directory. The submission is built in a fresh directory without its own prior build artifacts; official dependencies are reused only at their pinned, verified commits. The source has no admitted proof terms, custom axioms, opaque assertions, or `native_decide`.

Native LaTeX compilation was attempted and its platform-directory failure was recorded. The existing Tectonic installation exported the final two-page PDF without warnings. Both final rendered pages were opened and visually inspected successfully.

The authoring agent performs a self-review. Parent review and a current upstream source/duplicate check are separate publication gates; this agent does not write to GitHub.
