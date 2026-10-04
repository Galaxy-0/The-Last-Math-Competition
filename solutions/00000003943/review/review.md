# Solution Review — Conjecture 00000003943 (PR 372)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004021158`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — worst-case total number of augmenting paths in the classical augmenting-path matching algorithm is Θ(n² log n) with upper/lower ratio ≤ 2 (disproof: it is exactly ⌊n/2⌋, i.e. Θ(n)).
- LaTeX: compiled from scratch in /tmp/tlmc-review5/scratch/pr-372 (pdflatex twice, exit 0, 3 pages, no errors); shipped report.pdf is a real PDF whose extracted text is identical to the recompile.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, zero warnings, "Build completed successfully"; toolchain leanprover/lean4:v4.19.0, self-contained (imports only Std, empty manifest packages); `#print axioms` shows only [propext, Classical.choice, Quot.sound] for all four audited theorems.
- Forbidden content: grep over all .lean files for `sorry`, `admit`, `native_decide`, `axiom` declarations, `unsafe`, `@[implemented_by]`, `extern`, `skipKernelTC` — nothing found.
- Auxiliary code: `python3 verify.py` exit 0, output exactly matches verification/python-output.json (PASS; 1100 graphs, 10313 matchings, 20877 augmenting paths exhaustively checked through 5 vertices; tight disjoint-edge family through n=100). I independently re-derived the core fact (each augmentation raises |M| by 1, 2|M| ≤ n ⇒ k ≤ ⌊n/2⌋) by hand; verify.py's toggle checks corroborate.
## Semantic audit
Conjecture (literal, EN+CN): "In the worst case the total number of augmenting paths is Theta(n^2 log n), and the ratio between the upper and lower bounds is at most 2" / "最坏情形下增广路径总数为 Θ(n² log n)". The submission counts exactly what the algorithm's name denotes: paths selected and used for augmentation (增广路径总数). The report (Sec. 1) explicitly distinguishes this from failed searches / candidate enumerations, which the statement does not define.

Lean encodings of the conjecture's objects are faithful:
- `structure Matching (g : Graph)` — canonical edges, in-graph, `Nodup` endpoints (pairwise disjoint), bounded by `g.order`; `theorem matching_bound … : 2 * m.edges.length ≤ g.order` is the capacity fact.
- `structure AugmentingPath {g} (m : Matching g)` — `simple : nodes.Nodup`, `evenNodes : nodes.length % 2 = 0` (odd edge count), alternating membership (`alternatingFree`, `alternatingMatched`), `edgesInGraph`, unmatched endpoints (`startFree`/`endFree : ∀ v, edge nodes.head! v ∉ m.edges`, exactly equivalent to "endpoint unmatched" under canonical edges).
- `inductive Run … | step (path : AugmentingPath initial) (update : next.edges = toggle initial.edges path.nodes) (tail : Run next final k)` — every intermediate state is a `Matching`, so the run records the actual algorithm's invariant; `run_size`/`run_bound` give `final.edges.length = initial.edges.length + k` and `2 * k ≤ g.order`.
- The conjecture's lower-bound half is encoded as a necessary condition and refuted: `def ClaimedLowerBound : Prop := ∃ c N : Nat, 0 < c ∧ ∀ n : Nat, N ≤ n → ∃ g : Graph, g.order = n ∧ ∃ initial final : Matching g, ∃ k : Nat, Run initial final k ∧ n*n*Nat.log2 n ≤ c*k` and `theorem conjecture_00000003943_false : ¬ ClaimedLowerBound` (choosing n = c+N+2: n² ≤ n²·log₂n ≤ c·k ≤ c·n < n²). Any genuine Θ(n² log n) lower bound would imply this encoding (reciprocal integer constant, base change absorbed by constant factors — justified in report Sec. 3).

(i) Definitions faithful: real graphs, matchings, simple alternating augmenting paths, the symmetric-difference toggle (`toggle m p = removeEdges m (matchedEdges p) ++ freeEdges p`, `augmentation_size : |toggle| = |M|+1`). (ii) Hypotheses satisfied: the bound applies to every run from any initial matching — no shortest-path or empty-start assumption. (iii) Contradiction: universal k ≤ n/2 (in fact k ≤ ⌊n/2⌋ − |M₀|) contradicts an Ω(n² log n) worst case; tightness ⌊n/2⌋ shown in the report and verified. (iv) Not vacuous: the theorem quantifies over actual algorithm runs (a superset of the classical algorithm's runs, since early stop is allowed), so the universal upper bound covers every real run. The only un-formalized step — that the toggle of a simple augmenting path is again a matching — is proved in the report (Lemma 1) and holds in `Run` by construction of `next : Matching g`; this is disclosed in the README and report Sec. 4 and does not weaken the disproof (the bound needs only |M|-increase, which is formalized).

This is not a degenerate/edge-case counterexample: it is a universal linear upper bound valid for all graphs, initial matchings, and tie-breaking, against a claimed quadratic-log growth. No standard quantity of the classical algorithm (augmentations, searches, total work) is Θ(n² log n); the literal bilingual claim is simply false.
## Issues found
none blocking
## Verdict rationale
The mathematical content is the standard, correct argument that each augmentation increases the matching cardinality by exactly one while 2|M| ≤ n, giving at most ⌊n/2⌋ augmentations — flatly contradicting Θ(n² log n). The Lean project is self-contained (Std only), builds clean with no sorry/axioms/native_decide, formalizes the actual objects (graphs, matchings, augmenting paths, runs) and the asymptotic negation; LaTeX recompiles identically to the shipped PDF; verify.py runs, matches its records, and its exhaustive checks are genuine. Folder name pattern `ziangni-sys_submission_20261004021158` conforms.

## Disposition
APPROVED — merged into main (PR 372). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
