# Solution Review — Conjecture 00000003848 (PR 638)

**Submission:** Jackmeson1 — `solutions/00000003848/Jackmeson1_submission_20261005064834`
**Head:** `a68b5ad1baa81dee448fa31f7845e4e4479403f1`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06
**Result:** Approved

## Checklist results

- Official conjecture (`conjectures/00000003848.md`, English + Chinese) read in full; the submission's `conjecture.md` is byte-identical to it. Source-md check: pass.
- LaTeX report read in its entirety; independent `latexmk -pdf` rebuild succeeded; extracted text of shipped and rebuilt PDFs matches modulo standard glyph/ligature extraction artifacts (the `ffi` ligature in "affine" accounts for nearly every diff hunk). PDF-match check: pass.
- `lake build` (Lean v4.33.1, Mathlib v4.33.1) exits 0 with zero errors and zero warnings. Lean-build check: pass.
- No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. `#print axioms` for all four decisive theorems (`not_cellCoreDictionary`, `affineA1_jTrivial`, `affineA1_failures_infinite`, `not_cellCoreDictionary_one`) → `[propext, Classical.choice, Quot.sound]` only, independently re-run via the shipped `Axioms.lean`. Axiom check: pass.
- Auxiliary `verification/` material agrees with independently reproduced results; the single stale SHA256SUMS entry (`conjecture.md`) hashes the CRLF newline variant — bookkeeping artifact, content identical. Aux check: pass.
- Semantic audit: pass (details below).

## Semantic audit

This is a disproof, and it succeeds at two independent levels. The universal level needs nothing about 0-Hecke monoids: the conjecture asserts a bijection between two-sided cells and `(n+1)`-cores such that the number of left cells of a cell equals the number of distinct parts of the stripped core. But the empty partition has no cells, hence no hooks, hence is a `(n+1)`-core (`isCore_bot`), has 0 distinct parts (`distinctParts_bot`), and is fixed by any hook-removal operation (the Lean `strip` is an arbitrary map with hypothesis `strip ⊥ = ⊥`, satisfied by every reasonable model of rim-hook removal, since there is nothing to remove); the cell paired with it under any bijection would need 0 left cells, while every two-sided cell `C = jClass x` contains at least the left cell `lClass x` (`lClass ⊆ jClass`, `numLeftCells_ne_zero`). So `not_cellCoreDictionary` refutes the dictionary for every `n` and every admissible `strip`. This is decisive for the statement as written: the count formula fails at the empty core no matter what the cell structure is.

The second level answers the natural objection that the empty core is degenerate. For `n = 1` the submission analyzes the actual monoid. The Coxeter matrix of type `A_1^{(1)}` on two nodes has `m_{01} = ∞` (encoded as 0, Mathlib's convention) — this is correct: the affine `Ã₁` Weyl group is the infinite dihedral group — so the 0-Hecke monoid is `<π₀, π₁ | π₀² = π₀, π₁² = π₁>` with no braid relation. The submission realizes it by an action on words (`act i` prepends `i` unless the word already starts with `i`), verifies the relations (`actHom`), constructs the alternating normal form `eval m = actHom m []` with an explicit left inverse (`sec`, using `π_i π_i = π_i`), hence injectivity of `eval`, and proves length monotonicity with the absorption case analysis (`actHom_length`, `eval_prefix`). From `x = a·y·b` and `y = c·x·d` the chain of lengths `ℓ(y) ≤ ℓ(ay) ≤ ℓ(ayb) = ℓ(x) ≤ ℓ(cx) ≤ ℓ(cxd) = ℓ(y)` collapses, giving `ay = y`, then `yb = y`, then `x = y`: the monoid is J-trivial (`affineA1_jTrivial`), every two-sided cell is a singleton with exactly one left cell (`numLeftCells_affineA1`). Meanwhile the staircase partitions `δ_k = (k, k−1, …, 1)` are 2-cores (all hook lengths `2(k−i−j)−1` are odd) with exactly `k` distinct parts, so for every bijection the formula fails at all `δ_k`, `k ≥ 2` — an infinite, non-degenerate failure set (`affineA1_failures_infinite`, `not_cellCoreDictionary_one`). I checked the staircase hook computation and the J-triviality argument by hand; both are correct.

Faithfulness: the definitions follow the conjecture's own first sentence (two-sided cells = two-sided equivalence classes, i.e. Green `J`-classes `MxM = MyM`; left cells = `L`-classes `Mx = My`; both proved to be equivalence relations), the hook length is arm + leg + 1, a `t`-core has no hook length divisible by `t` (equivalent to having no hook of length exactly `t` for the cases used — the report even proves the equivalence argument via β-sets in prose and notes only ∅ and staircases are needed), distinct parts = distinct positive row lengths, and the number of left cells is an `ℕ∞`-valued count of `L`-classes inside the `J`-class. The 0-Hecke presentation (idempotent generators plus braid relations for finite labels only) is the standard `H_0` convention. The strip operation is treated at its weakest — any map fixing cores — so the refutation does not depend on a model of rim-hook tableau mechanics.

Build hygiene: zero errors/warnings; all four decisive theorems depend only on the three standard axioms, replayed independently.

## Issues found

- Minor: one entry of `verification/SHA256SUMS.txt` (`conjecture.md`) hashes the CRLF newline variant (verified by re-hashing after newline normalization). Non-blocking hygiene issue.

## Verdict

APPROVED. The disproof is two-tiered and rigorous: the count formula fails at the empty core for every type rank `n` (no bijection can satisfy it), and, avoiding the degenerate core entirely, the type `A_1^{(1)}` 0-Hecke monoid is proved J-trivial so that every cell has one left cell while infinitely many 2-cores (the staircases with ≥ 2 parts) demand more. The formalization is faithful to the conjecture's own definitions, and the build and axiom profile are clean.
