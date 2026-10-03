# Solution Review — Conjecture 00000003483 (PR 334)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003104000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — equality e = (5v−2)/3 for four-critical graphs is "attained only by nearly-four-regular doubly critical graphs" (plus a secondary edge-count lattice clause); submission refutes the necessary double-critical part.
- LaTeX: compiled ok (pdflatex x2, exit 0, 0 errors, 2 pages); shipped main.pdf is a real PDF v1.5, 2 pages (decompressed object count confirms), 43 KB; its SHA256 matches verification.json.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, "Build completed successfully", warnings-as-errors enabled; toolchain v4.19.0; no warnings.
- Forbidden content: the only grep hit for "admit" is line 77 of Main.lean — English prose ("deletions, admit three colors") inside the block comment `/- Strong criticality: ... -/` (lines 76–78), not the `admit` tactic. No `sorry`, `native_decide`, `axiom`, `unsafe`, `@[implemented_by]`, `extern`. Final theorems depend only on [propext, Quot.sound].
- Auxiliary code: no executable script is shipped (verification.json: auxiliary_scripts_rerun: []). I reproduced every field of the static record independent-check.json with my own Python brute-force (3^7 colorings, independent code): vertexCount 7, edgeCount 11, 3e=33=5v−2, 0 proper 3-colorings, proper 4-coloring exists, all 7 vertex deletions and all 11 edge deletions 3-colorable, witness edge {0,2}, surviving triangle {4,5,6}, deletion of {0,2}: 0 two-colorings, 216 three-colorings — all fields MATCH. All recorded SHA256 hashes match the on-disk files.
- Folder name: `gaochengzhecpu_submission_20261003104000` — matches the pattern.
## Semantic audit
Conjecture (English): "Equality is attained only by nearly-four-regular doubly critical graphs." Double-critical (standard, per KPT cited in the report): deleting both endpoints of every edge lowers χ by two. Key Lean definitions:
- `Adj G u v` on `Graph := List (Nat × Nat)`; `NormalizedSimple K := K.Nodup ∧ ∀ e ∈ K, e.1 < e.2 ∧ e.2 < 7` — so the verified list length IS the undirected edge count (`G_edge_count : G.length = 11`, `G_attains_equality : 3 * 11 = 5 * 7 - 2`).
- `ChromaticNumberIs K r` = (∃ proper r-coloring) ∧ (∀ k < r, no proper k-coloring) — exact chromatic number; `chromatic_four` legitimately excludes k < 4 by embedding Fin k into Fin 3.
- `FourCritical K = ChromaticNumberIs K 4 ∧ AllProperSubgraphsThree K` where `AllProperSubgraphsThree` quantifies over ARBITRARY `present : V → Prop` and symmetric `A` with the subgraph property and properness (∃ missing vertex ∨ ∃ missing K-edge), discharged by the symbolic `proper_subgraph_bridge` from the per-vertex/per-edge certificates (`tuple_eta` identifies arbitrary colorings with their 7 values). This is the full standard definition of 4-critical.
- `DoubleCriticalFour K = Connected K ∧ ChromaticNumberIs K 4 ∧ ∀ a b, Adj K a b → PairDeletionChromaticNumberIs K a b 2` — standard double-criticality for 4-chromatic graphs; `PairDeletionChromaticNumberIs ... 2` is the exact χ = k−2 = 2 condition.
Final theorems:
- `G_four_critical : FourCritical G`, `G_attains_equality : 3 * G.length = 5 * 7 - 2`
- `G_not_double_critical : ¬ DoubleCriticalFour G` (edge {0,2}: surviving triangle {4,5,6} forces χ(G−{0,2}) = 3 via `G_pair_not_two`/`G_pair_chromatic_three`)
- `conjecture3483_counterexample : ¬ EqualityForcesDoubleCritical` where `EqualityForcesDoubleCritical : ∀ K, NormalizedSimple K → FourCritical K → 3 * K.length = 5 * 7 - 2 → DoubleCriticalFour K`.
G is the Hajós join of two K4s (7 vertices, 11 edges: 02,03,05,06,12,13,14,23,45,46,56). It attains 3e = 5v−2, is 4-critical (verified against every proper subgraph, not a sampling), and is not double-critical. The formalized implication is exactly the necessary double-critical conjunct of "attained only by nearly-four-regular double-critical graphs": any extra "nearly-four-regular" conjunct would only strengthen the conclusion, so refuting the weaker necessary claim refutes the conjecture's clause. The hypotheses are satisfied by G; nothing is vacuous; the chromatic-number objects at issue are genuinely present (unlike the rejected PRs #286–288 pattern). LaTeX matches Lean: same edge list, same 4-coloring (0,0,1,2,1,2,3), identical vertex/edge-deletion color tables, same witness edge {0,2} and triangle {4,5,6}.
## Issues found
- The conjecture's own preamble calls the KY bound an "upper bound" (KY is a lower bound on e for 4-critical graphs). The submission's refutation uses only the equality condition e = (5v−2)/3 and explicitly does not rely on the direction; non-blocking.
- No executable auxiliary script is shipped; the computational record is a static JSON. I independently reproduced all of its fields, so this is non-blocking.
## Verdict rationale
Fresh Lean build clean under warnings-as-errors with only standard axioms; LaTeX compiles to a matching 2-page PDF; my independent brute-force enumeration reproduces every recorded computational claim (4-criticality, equality 3·11 = 5·7−2, χ(G−{0,2}) = 3). The Lean encodes the standard notions of 4-criticality and double-criticality over all colorings and all proper subgraphs, and the Hajós-join graph genuinely satisfies the equality while failing double-criticality, refuting the conjecture's necessary clause as stated.

## Disposition
APPROVED — merged into main (PR 334). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
