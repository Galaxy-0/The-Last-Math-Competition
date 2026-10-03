# Solution Review — Conjecture 00000003486 (PR 307)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — pairs of non-isomorphic four-critical graphs with identical single-deletion chromatic spectra exist, and the minimal such pair has thirteen vertices (with a completeness clause about the Mycielski framework).
- LaTeX: compiled ok (pdflatex twice, exit 0, 2 pages, 131 KB); included main.pdf is a real PDF (2 pages, 41 KB, verified); tex and pdf agree.
- Lean build: fresh build after `rm -rf .lake`, exit 0, no warnings (warnings-as-errors active), v4.19.0, imports only Std.
- Forbidden content: the only grep hit for "admit" is line 108, the English verb inside the block comment `/- Strong criticality: all proper subgraphs, including vertex and edge deletions, admit three colors. ... -/` — a comment, allowed. No sorry/native_decide/axiom/unsafe/implemented_by/extern. `#print axioms` on all five main results: [propext, Quot.sound] only.
- Auxiliary code: none present (records `auxiliary_scripts_rerun: []`, consistent). All recorded sha256 file hashes match current files; official conjecture sha256 = original_source_sha256. My independent brute-force Python check: χ(G)=χ(H)=4; all 7 vertex deletions and all 11/12 edge deletions of both graphs are 3-colorable; deletion spectra (3,3,3,3,3,3,3) identical; no isomorphism among all 5040 vertex bijections; G has two vertex-disjoint triangles, H has none; |E(G)|=11, |E(H)|=12.
## Semantic audit
Conjecture (literal): "There exist pairs of four-critical graphs with identical single-deletion chromatic spectra yet non-isomorphic graphs; the minimal counterexample pair has thirteen vertices..." The disproof refutes the minimality clause: a valid pair exists at order 7 < 13. The submission explicitly does not claim the true minimum (SOURCE.md scope note).

Objects: G and H are defined by the exact displayed edge lists (G = Hajós join of two K4's, H = Mycielskian of K3). `Adj` is symmetric list membership; `graphs_simple` kernel-checkes loop-freeness and symmetry. Colorings are functions V → Fin k with `Proper G c := ∀ u v, Adj G u v → c u ≠ c v`.

Exhaustiveness: the linchpin `tuple_eta` proves every function V → Fin k equals `tuple (c 0) ... (c 6)`, so the kernel-checked rejections (`G_no_three_tuple` over all 3⁷ tuples, `G_vertex_no_two_tuple` over all 2⁷ for each deleted vertex, same for H) exclude ALL colorings, not a sample.

Strong criticality: `ChromaticNumberIs K r := (∃ proper r-coloring) ∧ (∀ k < r, ¬∃ proper k-coloring)` — the honest chromatic number (minimality over all smaller k, with a coercion handling k ≤ 3). `AllProperSubgraphsThree K` quantifies over arbitrary subgraphs (vertex predicate + symmetric adjacency contained in K) that are proper, and asserts 3-colorability; `proper_subgraph_bridge` reduces this to vertex- and edge-deletion certificates (every proper subgraph omits a vertex or an edge of K), which are kernel-checked. `FourCritical K := ChromaticNumberIs K 4 ∧ AllProperSubgraphsThree K` is exactly "4-chromatic + every proper subgraph 3-colorable". `G_four_critical`, `H_four_critical` hold.

Spectrum: `DeletionChromaticNumberIs K x r` is the exact chromatic number of K−x (achievability + minimality); `same_deletion_spectrum : ∀ x, DeletionChromaticNumberIs G x 3 ∧ DeletionChromaticNumberIs H x 3` — both spectra are (3,...,3), identical.

Non-isomorphism: `Isomorphic K L := ∃ bijective f, ∀ u v, Adj K u v ↔ Adj L (f u) (f v)`; `graphs_not_isomorphic : ¬Isomorphic G H` maps G's two vertex-disjoint triangles {1,2,3}, {4,5,6} through any isomorphism (injectivity gives Nodup) and contradicts the kernel-checked `H_no_disjoint_triangles`. This covers all bijections structurally.

Final refutation: `NoSevenVertexPairClaim := ∀ K L, FourCritical K → FourCritical L → (∀ x, both deletion chromatic numbers are 3) → Isomorphic K L` — the order-7 consequence of "minimal pair has thirteen vertices". `not_minimum_thirteen_consequence : ¬NoSevenVertexPairClaim` instantiated at G, H, plus `counterexample_order_less_than_thirteen : 7 < 13`. The hypotheses of the conjecture's pair-existence clause are all satisfied by G, H and the claimed thirteen-vertex minimality is contradicted. Not vacuous — the actual graphs, colorings, chromatic numbers, and isomorphisms are the conjecture's objects.

LaTeX/Lean match: identical edge lists, identical coloring tables (spot-checked several rows), identical invariant (disjoint triangles, used in Lean; edge counts stated in tex), same theorem names.
## Issues found
- Interpretive (non-blocking, worth a human glance): "chromatic spectrum" is read as the multiset of chromatic numbers of single-vertex deletions (supported by the Chinese 色数谱, "chromatic-number spectrum"; for 4-critical graphs every deletion has χ=3, so any two non-isomorphic 4-critical graphs of equal order form a "pair"). Under the alternative stronger reading — multisets of chromatic POLYNOMIALS of deletions — this G,H pair would not qualify (11 vs 12 edges give different polynomial coefficient sums). The refutation of the "thirteen" clause is valid under the chromatic-number reading; under the polynomial reading the conjecture's minimal-pair claim would need separate study. Given the bilingual wording, the chromatic-number reading is the faithful one.
- Minor (non-blocking): the existential clause and Mycielski completeness clause of the conjecture are not separately addressed; unnecessary, since the refuted minimality clause already falsifies the conjunctive conjecture.
## Verdict rationale
The submission compiles cleanly with no placeholders, formalizes strong 4-criticality with genuinely exhaustive kernel checks (via tuple_eta, which extends the finite tables to arbitrary colorings), proves identical exact deletion chromatic spectra, excludes all isomorphisms structurally, and thereby refutes the conjecture's "minimal pair has thirteen vertices" with a seven-vertex pair. My independent brute-force confirms every claim. The only judgment call is the reading of "chromatic spectrum", and the chromatic-number reading is the faithful one to the bilingual statement.

## Disposition
APPROVED — merged into main (PR 307). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
