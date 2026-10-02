# Conjecture 00000000048: FALSE

Submitter: [SucRunBug](https://github.com/SucRunBug). AI-assisted mathematical work and Lean formalization.

A one-edge tree defeats the filed logarithmic label bound.

## Scope

Lean proves that the actual simple graph on Fin 2 is a tree with one edge, and proves that no injective real labeling into the filed interval exists, for every real C.

The complete argument and all interpretation boundaries are in `main.tex` and `main.pdf`. The readable PDF is rendered from the same proof text; it is not an export of the native LaTeX preview.

## Reproduce

```sh
python3 reproduce.py
cd lean4
lake exe cache get
lake build
lake env lean Check.lean
```

Lean and Mathlib v4.33.0; Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d. Only standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`) are permitted. No incomplete proofs, custom axioms or `native_decide`.

## Verification

`lake build`, `lake env lean Check.lean`, and independent Python checks passed. The native LaTeX compiler returned success. Actual outputs and source hashes are recorded in `verification.txt`. Final PDFs are visually inspected before publication. Organizer acceptance and ranking require official review.
