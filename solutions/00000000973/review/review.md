# Solution Review — Conjecture 00000000973 (PR 428)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004081504`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** The three-dot diff adds only the correctly named personal submission directory. Base metadata marks conjecture 00000000973 unsolved; there is no prior or removed solution. The submitted bilingual conjecture copy is byte-identical to the official file.
- **LaTeX and PDF.** I read the complete three-page report and every submitted source/config file. A fresh `latexmk -pdf` build succeeded (exit 0; 3 pages). Text extraction, normalized comparison, and Ghostscript rendering of every page confirmed the shipped and fresh reports match in content and structure. No auxiliary computation is needed.
- **Lean.** Using the official shared pinned Mathlib dependency tree, `lake build` completed successfully. Direct strict replay of `Jordan.lean`, `BoundedSet.lean`, `Conjecture973.lean`, and `Check.lean` exited 0 each. The audit prints the full matrix spectrum, polynomial evaluation, operator-norm, spectral-set, and final theorem types. Seventeen central axiom audits all report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, implementation override, external implementation, kernel-skip, or trust override occurs. Only legitimate `#print axioms` lines contain “axioms”.
- **Independent check.** I numerically verified the report's illustrative matrix `[[0,5],[0,0]]`: spectrum `{0}`, Euclidean operator norm `5`, and supremum `4` on the two indicated unit disks, hence `5>4`.

## Semantic audit

The official definition quantifies over every `n×n` matrix whose spectrum lies in `K`; it imposes only spectrum containment, with no normality, contractivity, or resolvent condition. Lean formalizes that literal definition using Mathlib's actual complex matrix spectrum, `Polynomial.aeval`, the canonical Euclidean operator norm, and the real supremum of polynomial values on `K`.

Let `K` be any nonempty bounded complex set. Choose `λ∈K` and `B` with `|z|≤B` for all `z∈K`. Set `D=|B|+|λ|`, `R=D+1`, and

`J = [[λ,R],[0,λ]], p(z)=z-λ`.

The resolvent determinant is `(z-λ)^2`, so the actual spectrum is exactly `{λ}⊆K`. Moreover `p(J)=[[0,R],[0,0]]`. On Euclidean vectors this sends `(u,v)` to `(Rv,0)`, whose norm is `R|v|≤R‖(u,v)‖`, with equality at `(0,1)`; hence the operator norm is exactly `R`. Lean proves both the lower and upper bounds and therefore the exact norm.

On the other hand, for every `z∈K`, `|p(z)|=|z-λ|≤|z|+|λ|≤D`. The image set used in the supremum is nonempty and bounded above, so its real supremum is at most `D<R=‖p(J)‖`. This strictly violates the stated von Neumann inequality in order two. No compactness or attained supremum is needed.

Every union of two positive-radius disks—open or closed—is nonempty and bounded. The closed-disk theorem covers arbitrary centers/radii with one nonempty disk, and the open-disk theorem handles the usual positive-radius interpretation. Since `2<15`, the conjecture's explicit assertion that all matrices of every order below 15 satisfy the inequality is false. This necessary clause is refuted without interpreting the vague minimal-order wording or deciding the separate order-33 claim.

The counterexample is non-vacuous: `K` is genuinely nonempty and bounded, the Jordan matrix's spectrum is genuinely contained in `K`, and both sides of the inequality use the formal supremum and actual operator norm. The report correctly distinguishes this literal all-matrices definition from the usual operator-relative notion of spectral set.

## Verdict rationale

The formalization faithfully follows the official wording and gives a universal algebraic obstruction for every bounded set. The Jordan spectrum and operator norm are proved, not assumed; the two-disk case follows rigorously; and all builds, replays, scans, and audits pass.

## Disposition

APPROVED — ready for merge (PR 428). No merge action was taken by this reviewer.
