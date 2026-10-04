# Verification record

Verification date: 2026-10-04 (UTC).

## Eligibility

The conjecture's metadata was unsolved when selected. The upstream solution tree for ID 00000006672 was empty. Direct repository PR search, including both open and closed PRs, returned no existing submission:

```sh
git ls-tree -r --name-only upstream/main -- solutions/00000006672
gh pr list --repo The-Last-Math-Competition/The-Last-Math-Competition --state all --search 00000006672 --limit 30
```

Both checks were repeated before this submission was prepared.

## Lean

- Official Lean 4.19.0 Windows binary.
- Mathlib v4.19.0, commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
- Downloaded Mathlib's official targeted cache for `Mathlib/Data/Real/Basic.lean`, `Mathlib/Analysis/Convex/Extreme.lean`, and `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean` (1195 files, all successful).
- The initial ProofWidgets release fetch failed transiently; `lake -v build proofwidgets:release` succeeded, after which the cache command succeeded.
- The submission's ignored `.lake/packages/` directory used local junctions to these exact pinned dependency checkouts during verification. They are not part of the submission or its public dependency configuration.
- The checked-in manifest extends the pinned Mathlib manifest with the exact root dependency revision. All entries use public Git URLs and immutable revisions.
- The long Windows submission path caused Lake to report absent `.olean.hash` files that actually existed. Mapping this submission's `lean` directory to the unused drive `T:` resolved the path limit.
- From that mapping, the final standalone `lake build` completed successfully (1208 tasks); see `lean-build.txt`. `Main` was compiled from this submission's source.
- The independent source invocation `lake env lean Main.lean` also succeeded; its exact output is in `axioms.txt`.

The axiom audit prints only `propext`, `Classical.choice`, and `Quot.sound`. All submitted proof terms were checked by Lean. The formal graph and convex-extremality definitions come from Mathlib; the matrix constraints and positive-support adjacency are explicit in `Main.lean`.

## Report

The source was opened in the built-in LaTeX editor. Its compiler returned the platform error `Unable to find standard directories for platform`, so the installed Tectonic compiler was used for the exported PDF:

```sh
tectonic report.tex --keep-logs
pdfinfo report.pdf
pdftoppm -scale-to 1400 -png report.pdf <scratch-output-prefix>
```

The final Tectonic run succeeded, with no overfull or underfull box warnings. It emitted a nonfatal host Fontconfig configuration message; the PDF contains the intended embedded fonts. `pdfinfo` reported two A4 pages. Both rendered pages were visually inspected for clipping, collisions, mathematical notation, page numbering, and readability. No layout defects remained.

The full proof is symbolic. The supporting rank/basis discussion explains the distinction in the original wording; the disproof and its formal theorem require only feasibility, extremality, and disconnected positive support.
