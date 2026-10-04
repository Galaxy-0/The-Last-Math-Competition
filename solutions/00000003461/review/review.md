# Solution Review — Conjecture 00000003461 (PR 352)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — DP-coloring (Bernshteyn–Kostochka–Pron): χ_DP(planar) ≤ 5, girth ≥ 5 planar ⟹ χ_DP ≤ 3, difference spectrum χ_DP−χ on planar class is exactly {0,1}, and the smallest graph attaining 1 is the three-dimensional prism.
- LaTeX: recompiled twice with pdflatex, exit 0 both, 2 pages; shipped main.pdf is a real PDF 1.5 whose gs-extracted text matches main.tex.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings, Lean 4.19.0, Std only (`set_option maxHeartbeats 20000000` / `maxRecDepth 100000` present — performance options, not soundness-relevant).
- Forbidden content: none — grep for sorry/admit/native_decide/axiom/unsafe/implemented_by/extern/skipKernelTC empty; `#print axioms` shows only [propext, Quot.sound, Classical.choice] — the three standard Lean axioms.
- Auxiliary code: no Python/JS shipped; I ran my own independent exhaustive enumeration instead: all 1-fold (1), 2-fold (16), and 3-fold (1296) covers of C4 checked — k=1 uncolorable, k=2 has 8 uncolorable covers (incl. the twisted identity/identity/identity/swap cover), k=3 all colorable. Confirms χ(C4)=2, χ_DP(C4)=3 exactly.
## Semantic audit
Conjecture (bilingual; conjecture.md byte-identical, SOURCE.md identical modulo CRLF). The targeted clause: "the smallest graph attaining one [χ_DP−χ=1] the three-dimensional prism" (取一的最小图为三维双棱柱). Lean encodings:

- `def adjacent` on `Fin 4` — exact 4-cycle (loopless and symmetric proved); `Cover (Colors : V → Type)` with `conflict` relations that are symmetric, supported on adjacency, and matching (at most one partner per color) — a faithful general DP-cover (arbitrary per-vertex color types; partial matchings allowed, which only strengthens the universal upper bound); `AuxAdj` adds the fiber cliques and `independent_transversal_iff` proves avoidance ⟺ independent transversal — the standard BKP setup, matching the cited arXiv:1609.00763 definitions.
- `twisted : Cover (fun _ => Fin 2)` — identity matchings on edges 01,12,23, antidiagonal on 30; `checked_no_twisted_coloring` (all 16 selections, `by decide`) plus `tuple4_eta` (every function on Fin 4 is a 4-tuple, proved) give `twisted_not_colorable`; `oneCover`, `emptyCover` handle k=1,0 → `DPChromaticExactly 3`.
- `every_three_cover_colorable` — a genuine symbolic greedy proof over an ARBITRARY cover (not enumeration): at most one color forbidden per already-colored neighbor, at most two at the last vertex, so a third remains; `arbitrary_lists_of_size_at_least_three` transports to heterogeneous fibers of size ≥ 3 via an injective `pick`.
- `Proper`/`ChromaticExactly 2` — ordinary chromatic number of C4 exactly 2.
- `SquareEmbedding` — a planar-drawing certificate for C4: adjacency ⟺ edge-endpoint incidence; vertex injectivity, endpoint incidence, edge-trace injectivity, no vertex on an edge interior, and disjoint edge interiors, all universally quantified over arbitrary K, lo≠hi, and interior parameters t,u (so genuinely over all real t,u∈(0,1), not sampled points).
- `every_prism_larger (m) (hm : 3 ≤ m) : 4 < prismOrder m` (=2m) and final `theorem conjecture3461_false (m) (hm : 3 ≤ m) : ¬(SquareEmbedding → ChromaticExactly 2 → DPChromaticExactly 3 → prismOrder m ≤ 4)`.

C4 is planar with χ_DP−χ = 3−2 = 1 on 4 vertices; any prism over an m-gon (m ≥ 3), in particular the three-dimensional/triangular prism, has 6 vertices. The minimality clause is therefore false — this is the textbook example (BKP show χ_DP(C_n)=3 for cycles). Interpretation calls disclosed: (i) "smallest" read as fewest vertices (the natural reading of 最小图); under fewest edges C4 (4 edges) also beats the triangular prism (9 edges); (ii) the other clauses (planar χ_DP ≤ 5, girth-5 bound, spectrum = {0,1}) are untouched, but the conjecture is a conjunction and the minimality conjunct fails; (iii) the final theorem packages the minimality contradiction as "no m-prism has order ≤ 4 given C4's facts" — the bridge from the source's wording is spelled out in the tex. Not vacuous: C4 is concrete, all its properties proved unconditionally.
## Issues found
none blocking
## Verdict rationale
Clean build with only the three standard Lean axioms; the DP-cover formalization matches the BKP definition (arbitrary fibers, matchings, clique auxiliary graph, independent transversal); the lower bound is the standard twisted-cover argument with a proved totality bridge, the upper bound a symbolic greedy proof over arbitrary covers; and my independent exhaustive enumeration of all k-fold covers of C4 for k ≤ 3 confirms χ_DP(C4)=3, χ(C4)=2. The minimality clause of the conjecture is decisively false since 4 < 6.

## Disposition
APPROVED — merged into main (PR 352). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
