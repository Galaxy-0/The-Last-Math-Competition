# Solution Review — Conjecture 00000000541 (PR 345)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — shellability of the independence complex of a bipartite graph is claimed equivalent to chordality of the graph, with the criterion complete over chordal bipartite graphs.
- LaTeX: compiled (pdflatex twice, exit 0, 1 page); shipped main.pdf real PDF v1.5, text matches recompiled output (kerning-only differences).
- Lean build: exit 0, fresh (`rm -rf .lake && lake build`), Lean 4.19.0, `import Std`. Uses `set_option maxHeartbeats 100000000` and `maxRecDepth 1000000` (allowed); kernel `decide` only, no native_decide. Only output = `#print axioms` info lines.
- Forbidden content: none (grep zero matches). Axioms: [propext, Classical.choice, Quot.sound] throughout — standard; no sorryAx, no custom axioms.
- Auxiliary code: no Python/JS shipped; recorded verification logs match my fresh build. Independent python3 brute force over all 4096 subsets confirms: 18 facets, all of size 6 (pure), exactly the family F_I = {v_i : i∈I} ∪ {w_i : i∉I} for I independent in C_6; the Lean's 18 masks are precisely these facets; the pairwise facet-difference shelling criterion holds in the exact Lean facet order (and in the by-|I| order); the graph is bipartite under the stated 2-coloring and contains an induced 6-cycle (so neither chordal nor chordal bipartite).
## Semantic audit
Conjecture (literal): "Shellability of the independence complex of a bipartite graph is equivalent to the chordality of the graph; and the criterion is complete over the class of chordal bipartite graphs." The PR is a disproof: a bipartite graph whose independence complex is shellable while the graph is neither chordal nor chordal bipartite, killing the equivalence (and hence the conjunction).

Key Lean signatures (lean/Main.lean, namespace Conjecture541):
- `def whiskeredCycle : Graph` (v_i = i<6 on a 6-cycle, w_i = i+6 a leaf on v_i), `theorem graph_laws : GraphLaws whiskeredCycle` (irreflexive + symmetric).
- `theorem graph_bipartite : Bipartite whiskeredCycle`; `def InducedCycle G k f` (injective, edges exactly the cycle edges — a genuine induced-cycle embedding), `theorem induced_six_cycle : InducedCycle whiskeredCycle 6 cycleEmbedding`.
- `def Chordal (G) : Prop := ∀ k, 4 ≤ k → ∀ f, ¬InducedCycle G k f` — standard chordality; `def ChordalBipartite (G) : Prop := Bipartite G ∧ ∀ k, 5 ≤ k → ...` — equivalent to the standard "no induced cycles ≥ 6" for bipartite graphs (odd induced cycles cannot exist); `theorem not_chordal`, `theorem not_chordal_bipartite` — both readings of "chordality" refuted.
- `def Independent`, `def MaximalIndependent` (inclusion-maximal, correct), `def IsFacet` (independent + every outside vertex blocked), `theorem facet_iff_maximal` — proper equivalence between the computable facet test and genuine maximality, not a fiat.
- `theorem all_facets : ∀ s : Mask, IsFacet whiskeredCycle s ↔ ∃ j : Fin 18, s = facets j` — completeness of the 18-facet list, by kernel decide over all 4096 masks (64 blocks); `distinct_facets`, `facets_cardinality : ∀ j, cardinality (facets j) = 6` (purity).
- `def IsShelling G F := (∀ s, IsFacet G s ↔ ∃ j, s = F j) ∧ (∀ i j, F i = F j → i = j) ∧ ∀ i j, i < j → ∃ l, l < j ∧ ∃ v, member (F j) v = true ∧ member (F i) v = false ∧ ∀ w, (member (F j) w = true ∧ member (F l) w = false) ↔ w = v` — this is the standard facet-difference characterization of shellability (for each earlier F_i and current F_j there is an earlier F_l with F_j \ F_l = {v} and v ∈ F_j \ F_i), the criterion of the cited Morey–Reyes–Villarreal Def 2.7. I verified by hand that this pairwise criterion is equivalent to the pure-intersection topological definition for pure complexes (both directions: F_i∩F_j ⊆ F_j\{v} = F_j∩F_l), and the complex is pure (all facets size 6), so the criterion is legitimate here.
- `theorem shelling_certificate` (by decide over all ordered pairs), `theorem independence_complex_shellable : Shellable whiskeredCycle`, `theorem every_maximal_independent_set` (Prop-valued bridge — no subset is omitted).
- `theorem conjecture541_false : ¬(∀ G : Graph, GraphLaws G → Bipartite G → (Shellable G ↔ Chordal G))`.

My independent brute force confirms every numeric claim (18 facets, purity, shelling in the exact listed order, bipartiteness, induced C_6). The counterexample engages the conjecture's actual objects (independence complex facets, shellability, chordality, chordal bipartiteness) and directly falsifies the asserted equivalence under both readings of "chordality". This contradicts and thus refutes the conjecture's first clause; the second clause ("criterion complete over chordal bipartite graphs") falls with the conjunction.
## Issues found
- Minor: the equivalence between the facet-difference criterion and the topological definition of shellability is invoked from the literature (correctly) rather than reproved in Lean; acceptable for pure complexes, and purity is proved in-file.
- Minor: `ChordalBipartite` uses "no induced k-cycle for k ≥ 5" (standard is ≥ 6); equivalent for bipartite graphs, and `not_chordal_bipartite` is witnessed by an induced 6-cycle, so nothing is weakened.
## Verdict rationale
A substantive, self-contained kernel-verified disproof: real graph, real independence complex, real shelling certificate checked exhaustively, both chordality readings refuted, all confirmed by my independent brute-force computation. Fresh build exits 0 with only standard axioms. Meets the non-vacuity bar decisively.

## Disposition
APPROVED — merged into main (PR 345). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
