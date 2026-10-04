# Ulam sequence infinitude and a logarithmic counting bound

Conjecture: `00000000205`  
Submission account: `Galaxy-0`  
Prepared: 2026-10-04 UTC

For every integer n >= 2, this project constructs the standard Ulam sequence
U(1,n), proves its uniqueness and infinite range, and proves

    a_(r+2) <= n * 2^r
    A_n(n * 2^r) >= r + 2, for every integer r >= 0.

Each next term is the least integer above the previous term having exactly
one unordered representation as a sum of two distinct earlier values.
The report gives the complete mathematical proof, its exact relationship to
the formal declarations, and attribution for the known infinitude result.

## Important scope

The infinitude argument is a known elementary fact. This submission claims a
reproducible formalization and an explicit logarithmic counting estimate, not
a new discovery of infinitude. The competition's phrase "via density estimates"
does not specify a particular density assertion. This package proves the exact
counting estimate above. It does not prove positive natural density, positive
lower asymptotic density, or existence of a natural-density limit. If a stronger
density assertion is intended, that assertion is outside this submission.

## Files

- `report.tex`: complete LaTeX report
- `report.pdf`: four-page PDF compiled from that source
- `Ulam205Core.lean`: complete dependency-free Lean 4 formalization
- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`: Lean project setup
- `proof.zh-en.md`: bilingual proof and scope explanation
- `verification/`: compiler logs, audit, toolchain, and repository-status record
- `SHA256SUMS`: checksums for the files in this submission

## Verify the Lean proof

Use the official Lean 4.31.0 toolchain:
https://github.com/leanprover/lean4/releases/tag/v4.31.0

From this submission directory, with that toolchain's `lean` and `lake` on PATH:

```sh
lean --version
lean Ulam205Core.lean
lake build
```

With elan installed, `lean-toolchain` selects the version. The project has an
empty external dependency list; no Mathlib download is required. The compiler
binary and build cache are not bundled.

Both commands completed with exit code 0 in the prepared submission directory.
The final Lean source is unchanged from the independently checked version:

    ddbc155f051e41efb27b719b3d08df58d1f33836d8e7f13bd551718863f0a887

The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
for the main theorem. Uniqueness uses `propext` and `Quot.sound`. There are no
proof holes, added axioms, or `native_decide` uses.

## Build the PDF

With a configured LaTeX installation containing the standard packages used by
`report.tex`, run twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The PDF was compiled from the included source and every page was visually
checked. The proof requires no numerical computations or auxiliary programs.

## Main formal statements

All declarations are in namespace `Ulam205Core`.

- `conjecture_00000000205`: the same constructed sequence satisfies the exact
  Ulam rule, strict increase, infinite range, the growth bound, and the finite
  injective counting statement.
- `sequence_unique`: any two sequences satisfying `IsUlam n` are equal.
- `stage_mem_iff`: each state contains exactly the earlier sequence values.
- `counting_lower_bound`: an injection from `Fin (r + 2)` into Ulam values at
  most `n * 2^r`.

Lean uses zero-based indexing: `u 0 = 1`, `u 1 = n`, and `u (r + 1) = a_(r+2)`.

## Submission layout

The official rules require a personal directory under the problem's
11-digit ID, with LaTeX, PDF, and Lean materials. This directory is prepared as:

    solutions/00000000205/Galaxy-0_submission_20261004024529/

Only this directory belongs in the pull request. Do not modify the repository's
conjecture descriptions, root README, leaderboard, metadata, or unrelated files.
The source archive is a prepared submission; publication and acceptance are
separate events. Recheck the problem's status immediately before opening a PR.

Rules: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/6ad05f1490626b518d19ad5c5603419f7a021d30/README.md
