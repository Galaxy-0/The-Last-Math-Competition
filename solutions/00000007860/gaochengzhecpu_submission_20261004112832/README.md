# Conjecture 00000007860: disproved as written

The claimed bound `W(G) <= n/2 - sqrt(n/2)` is false for the one-vertex edgeless graph. Its unique vertex order uses exactly one greedy color, its chromatic number is one, and its waste and uniform expected waste are zero. The proposed bound is `1/2 - sqrt(1/2) < 0`.

Both language versions say "for every graph" without an `n >= 2` restriction. This submission refutes that universal finite-graph conjunct. It does **not** resolve the separate asymptotic concentration formula for `G(n,1/2)`, proposed extremizers, or a modified inequality restricted to larger graphs.

## Contents

- `main.tex`, `main.pdf`: complete two-page proof and formalization correspondence.
- `SOURCE.md`: exact bilingual statement and source snapshot identity.
- `lean/Main.lean`: actual graph, permutations, first-fit algorithm, proper coloring, chromatic number, waste, finite uniform expectation, and counterexample theorems.
- `lean/lean-toolchain`, `lean/lakefile.toml`, `lean/lake-manifest.json`: portable pinned Lake project.
- `verify.py`: a separate exact execution of the exhibited singleton witness.
- `verification/BUILD.json` and adjacent logs: actual fresh-build evidence.
- `verification/SELF_REVIEW.md`: same-agent adversarial review and scope checks.

## Reproduce

Install Lean through elan, then run from `lean/`:

```text
lake build
lake env lean -DwarningAsError=true Main.lean
```

The toolchain is Lean 4.19.0. Mathlib is pinned to public Git commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; every transitive dependency is locked in `lake-manifest.json`. The project uses public Git URLs, with no local dependency paths. For a fresh machine, fetching the official Mathlib cache with `lake exe cache get` is optional but faster than rebuilding dependencies.

From the submission directory:

```text
python verify.py
tectonic main.tex
```

The auxiliary script uses only Python's standard library. Its graph-coloring enumeration checks this exact finite witness; it makes no claim based on searching only finitely many graph sizes.

## Actual verification

- A fresh directory containing the submitted Lean source and configuration passed `lake build` and direct Lean with warnings treated as errors.
- No proof gaps, admitted terms, custom axioms, opaque declarations, or `native_decide` occur in the submitted source. Printed theorem dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
- `verify.py` passed: one vertex order, empty forbidden set, greedy color count 1, chromatic number 1, waste 0, and uniform expectation 0. The negative radical bound is checked with exact rational squares.
- Tectonic compiled the final two-page PDF without warnings; both Poppler-rendered pages were visually inspected.
- The built-in source editor was requested, and native compilation was actually attempted. Its platform-directory failure is recorded in `verification/native-compiler.json`; the PDF is from the verified Tectonic run.

The clean build reused unmodified dependency artifacts at pinned official Git commits, but did not reuse this submission's own build outputs. Source hashes are recorded in `verification/BUILD.json`.

## Formalization boundary

`firstAvailable` is defined using the least natural number outside a finite forbidden set, with proofs of admissibility and minimality. `greedyRun` recursively assigns it using already processed neighbors. The singleton execution is proved exactly, and its assignment is matched to an actual Mathlib proper coloring. Mathlib's minimum proper-coloring number supplies the chromatic number; the waste is a derived real difference, not a declared constant.

The uniform expectation is represented by its defining finite average over all vertex permutations. The permutation count is positive in general and is one for the witness. No measure-theoretic probability model or asymptotic random-graph result is claimed. General correctness of the greedy routine for every graph is not needed or asserted: the witness's actual computed coloring and color count are both checked.

Authorship and review: this package received an authoring-agent self-review. Independent parent review and a current upstream duplicate/source check are pending before publication. No GitHub writes were performed by this agent.
