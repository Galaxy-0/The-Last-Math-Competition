# Solution Review — Conjecture 00000003464 (PR 353)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The L(2,1) span satisfies λ(G) ≤ Δ², with asymptotic equality attained only by Moore graphs of diameter two; the optimal upper bound Δ²−Δ+2 is exact for prime-power Moore graphs, and general graphs improve by a logarithmic correction in Δ" (span λ = minimal label range; distance-1 vertices differ ≥ 2, distance-2 differ ≥ 1).
- LaTeX: recompiled twice with pdflatex, exit 0 both, 1 page; shipped main.pdf is a real PDF 1.5 whose gs-extracted text matches main.tex.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings, Lean 4.19.0, Std only (`maxHeartbeats`/`maxRecDepth` performance options only).
- Forbidden content: none — grep for sorry/admit/native_decide/axiom/unsafe/implemented_by/extern/skipKernelTC empty; `#print axioms` shows only [propext, Quot.sound, Classical.choice].
- Auxiliary code: no Python/JS shipped; none needed (two-vertex computation re-derivable by hand: adjacent labels must differ ≥ 2 so any labeling's range ≥ 2; labels {0,2} achieve 2; Δ=1 so Δ²=1). verification/INDEPENDENT_REVIEW.md and VALIDATION.json consistent with my fresh build.
## Semantic audit
Conjecture (bilingual; conjecture.md byte-identical, SOURCE.md identical modulo CRLF). Both language versions assert λ(G) ≤ Δ² with no lower bound on Δ (猜想：L(2,1) 跨度满足 λ(G) ≤ Δ²). Lean encodings:

- `structure Graph n` (symmetric, loopless Bool adjacency on Fin n) — simple graphs; `degree`/`maxDegree` computed from the full vertex list — Δ(G).
- `def DistanceTwo G v w := v ≠ w ∧ G.adj v w = false ∧ ∃ u, G.adj v u ∧ G.adj u w` — distance exactly two; `def L21 G f` — adjacent ⟹ `2 ≤ separation (f v) (f w)`, distance-two ⟹ `1 ≤ separation` — exactly the conjecture's own definition (距离一差至少二、距离二差至少一); `separation a b := (a−b)+(b−a)` on Nat = |a−b|.
- `SpanAtMost f R := ∃ lo, ∀ v, lo ≤ f v ∧ f v ≤ lo + R` — the label range/极差 convention named in the source, with `span_range_equivalence` proving agreement with max−min; `MinimumSpan G s` — s is the least achievable span, i.e., λ.
- `edgeGraph : Graph 2` = K2: `maximum_degree_one : maxDegree edgeGraph = 1`, `no_distance_two` (second condition vacuous), `edgeLabels = {0,2}` with `labels_valid`, `labels_span_two`, and the symbolic `every_valid_span_at_least_two` (quantifies over ALL label values f : Fin 2 → Nat and ALL translates — no bounded search) ⟹ `edge_minimum_span : MinimumSpan edgeGraph 2`, i.e., λ(K2) = 2.
- `def ClaimedUniversalBound : Prop := ∀ n (G : Graph n), ∃ f, L21 G f ∧ SpanAtMost f (maxDegree G * maxDegree G)` — the conjectured λ(G) ≤ Δ² as an existence of a valid bounded-span labeling, equivalent to λ ≤ Δ²; final `theorem conjecture3464_false : ¬ClaimedUniversalBound` instantiates G := K2 and derives 2 ≤ 1.

Mathematics: λ(K2) = 2 > 1 = Δ(K2)² — adjacent vertices must differ by at least 2, so every labeling has range ≥ 2 regardless of magnitude; labels 0,2 attain it; Δ = 1. Airtight, and robust under either span convention (max-label or range: both give 2). Interpretation calls disclosed: the counterexample is the classical degenerate case Δ = 1 that the standard Griggs–Yeh formulation excludes with Δ ≥ 2 — the report explicitly says it does not disprove the Δ ≥ 2 version and cites the standard statement (Discrete Appl. Math. DOI 10.1016/j.dam.2025.10.011); but the bilingual text imposes no such restriction and, per the adjudicated literal-statement rule, the unrestricted universal bound (a necessary conjunct of the conjecture) is false. The Moore/asymptotic clauses concern Δ ≥ 2 graphs and are untouched, but a conjunction falls with one false conjunct. Not vacuous: concrete graph, exact minimum span proved both ways.
## Issues found
none blocking
## Verdict rationale
Everything compiles and runs cleanly with only standard axioms, the Lean definitions mirror the conjecture's own L(2,1)/span/Δ definitions, and the K2 counterexample is verified exactly (minimum span 2 proved symbolically over all labelings, Δ² = 1). The degenerate-case nature of the disproof is candidly disclosed and the bilingual statement contains no Δ ≥ 2 hypothesis, so under the authoritative literal reading the refutation is valid.

## Disposition
APPROVED — merged into main (PR 353). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
