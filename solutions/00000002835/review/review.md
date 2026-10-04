# Solution Review — Conjecture 00000002835 (PR 350)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "a rank-r matrix is uniquely recoverable on the support of graph G if and only if G contains an r-regular supported subgraph; the minimal observation count is the combinatorial correction of 2nr−r²" (deterministic matrix completion criterion).
- LaTeX: recompiled twice with pdflatex, both exit 0, 1 page; shipped main.pdf is a real PDF 1.5 whose gs-extracted text matches main.tex.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (`-DwarningAsError=true` set), Lean 4.19.0, deps: Std + Std.Internal.Rat only.
- Forbidden content: none — grep for sorry/admit/native_decide/axiom/unsafe/implemented_by/extern/skipKernelTC over lean/*.lean empty; `#print axioms` shows only [propext]. (`set_option maxRecDepth 100000` present — legitimate, not a soundness option.)
- Auxiliary code: no Python/JS shipped; independent verification done by me instead (below). verification/lean-axioms.log matches my fresh build output; VALIDATION.json consistent.
## Semantic audit
Conjecture (English = 中文, faithful in conjecture.md byte-identically; SOURCE.md identical modulo CRLF line endings): unique recoverability on support G ⟺ G contains an r-regular supported subgraph. Lean encodings:

- `abbrev Scalar := Std.Internal.Rat`, `Matrix := Fin 2 → Fin 2 → Scalar`, `Support := Fin 2 → Fin 2 → Bool` — actual rational 2×2 matrices and a boolean bipartite observation graph.
- `rank` is the determinantal rank (2 if det≠0, 0 if all entries 0, else 1) — exactly the standard rank for 2×2 over ℚ; certified redundantly by `all_two_minors_zero`, `nonzero_one_minors`, and outer-product factorizations `A=(1,1)ᵀ(1,1)`, `B=(1,−1)ᵀ(1,−1)` (`outer_products`).
- `ContainsRegularSubgraph G r` — ∃ nonempty selected row/col vertex sets and sub-support H ⊆ G with all edges inside the selection and every selected vertex of degree exactly r; permits spanning and nonspanning subgraphs, so it matches both readings of "subgraph".
- `UniquelyRecoverable G M := ∀ N : Matrix, rank N = rank M → SameObservations G M N → N = M` — uniqueness among ALL rational same-rank matrices (universal quantifier, not a finite table).
- Final: `def ClaimedCriterion : Prop := ∀ G M, rank M = 1 → (UniquelyRecoverable G M ↔ ContainsRegularSubgraph G 1)` and `theorem conjecture2835_false : ¬ClaimedCriterion`, refuting the sufficiency (⟸) direction at G = diagonal (perfect matching, 1-regular via `diagonal_one_regular`/`diagonal_contains_one_regular`) with A = all-ones, B = diag(1,−1) agreeing on observed entries (`same_observations`) but `distinct_completions`.

My independent Python re-derivation confirms: det-rank(A) = det-rank(B) = 1; A and B agree on the diagonal, differ off it; indeed a full one-parameter family {[[1,t],[1/t,1]] : t≠0} of rank-1 completions exists, so even a "generic matrix" reading of sufficiency fails on this support. The failure among exactly-rank-1 witnesses also implies failure under a rank ≤ r reading. Interpretation calls disclosed: (i) the counterexample is the 2×2, r=1 instance — a single falsifying instance of a universally quantified iff suffices; (ii) "uniquely recoverable" could mean among rank-exactly-r or rank-≤-r — the witness falsifies both; (iii) the conjecture's second clause (minimal observation count 2nr−r² correction) is untouched, but a conjunction falls when one conjunct falls. Not vacuous: concrete satisfiable support, concrete matrices, all hypotheses of the ⟸ direction hold.
## Issues found
none blocking (SOURCE.md has CRLF line endings vs the repo's LF — content byte-identical after newline normalization; conjecture.md byte-identical)
## Verdict rationale
The Lean formalization faithfully encodes the conjecture's own objects (rank via minors over ℚ, boolean bipartite support with vertex degrees, universal unique-completability), builds cleanly with only propext, and the final theorem genuinely contradicts the conjectured iff at a concrete instance. The mathematics was independently re-verified in Python, including robustness under alternative readings (rank ≤ r, generic matrix, spanning/nonspanning subgraph).

## Disposition
APPROVED — merged into main (PR 350). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
