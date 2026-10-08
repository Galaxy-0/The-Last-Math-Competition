# Local solution candidate: 00000001100

The standard finite-field affine group contains an inclusion-maximal origin
stabilizer with exactly two natural-action orbits. Prime fields of unbounded
size therefore refute even the eventual uniform `q + O(1)` count clause.

- `original.md`: exact bilingual input from upstream commit
  `6dc8261ea302809ca633aa6c0c903aa8acfacf1f`.
- `lean/Main.lean`: actual affine group, subgroup, orbit quotient and refutation.
- `source-correspondence.md`: definition and quantifier correspondence.
- `proof.tex` / `proof.pdf`: mathematical argument, compiled from the source.

From `lean/`, using Lean 4.33.0:

```
lake build +Main
```

`lake-manifest.json` pins mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d` and pins all eight dependencies.
The independent local project contains clean Git checkouts and its own build
cache. The manager preparation evidence records every local clone and the cache
provenance. No author-produced `.olean` is imported by the package verification.
On another machine obtain the dependencies from these exact lock revisions;
compile the imports and Main with the matching toolchain.

Compile the paper with Tectonic 0.17: `tectonic --untrusted proof.tex`.
The manager invokes the existing `scaling/hooks/check_submission.py` directly
using an external manifest, then binds an independent semantic review to the
frozen package bytes. Those receipts are external to this sealed package.

This package alone does not assert a verification status. Current submission
eligibility is unknown: the frozen metadata marks the input unsolved and the
per-ID PR query had no hits, but coverage is incomplete. No PR, push, first-solve
or upstream-acceptance claim is made. The construction is standard group theory.
