# Solution Review — Conjecture 00000004396 (PR 354)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "All Mobius ladders are Sidorenko, and every odd subdivision of a tree is Sidorenko, and the union of the two families gives infinitely many new nontrivial members" (Sidorenko graph = graph for which the reflection bound always holds).
- LaTeX: recompiled twice with pdflatex, exit 0 both, 1 page; shipped main.pdf is a real PDF 1.5 whose gs-extracted text matches main.tex (t(H,G)=hom(H,G)/|V(G)|^{|V(H)|}, t(H,G) ≥ t(K2,G)^{|E(H)|}).
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (`leanOptions = { warningAsError = true }`), Lean 4.19.0, Std only (`maxHeartbeats 40000000` is a performance option).
- Forbidden content: none — grep for sorry/admit/native_decide/axiom/unsafe/implemented_by/extern/skipKernelTC over lean/Main.lean empty; `#print axioms` shows only [propext, Quot.sound, Classical.choice].
- Auxiliary code: `verify.py` run with python3 — exit 0, printed JSON byte-equivalent (after key-sort) to the recorded `auxiliary-verification.json` and `verification/auxiliary-verification.log`: 8 vertices, the exact 12-edge list, 256 vertex maps, hom_to_K2 = 0, cross-multiplied sides [1048576, 0]. My own independently written script reproduced: M8 edges = C8 ∪ {{i,i+4}: i<4} (12 edges, identical list), hom(M8,K2) = 0, t(M8,K2) = 0 < 2^{−12} = t(K2,K2)^{12} (fails also at G = C4), 5-cycle 0-1-2-3-4-0 present, and contrast hom(M6,K2) = 2 (M6 = K_{3,3} bipartite), confirming M8 is a genuine non-bipartite Möbius ladder.
## Semantic audit
Conjecture (bilingual; conjecture.md byte-identical, SOURCE.md identical modulo CRLF): "All Mobius ladders are Sidorenko" (Mobius 梯图的全部为 Sidorenko). Lean encodings:

- `structure Graph n` (symmetric, loopless) — simple graphs; `edgeCount` via i<j pairs; `Hom H G f := ∀ i j, H.adj i j = true → G.adj (f i) (f j) = true` — arbitrary (not necessarily injective) edge-preserving vertex maps, exactly the homomorphisms of the tex definition.
- `def Sidorenko {m} (H : Graph m) : Prop := ∀ n, 0 < n → ∀ G : Graph n, ∀ maps, maps.Nodup → (∀ f, f ∈ maps) → (2 * edgeCount G)^edgeCount H * n^m ≤ homCount H G maps * n^(2 * edgeCount H)` — the exact cross-multiplied form of t(H,G) ≥ t(K2,G)^{e(H)} (using hom(K2,G) = 2e(G), the ordered adjacent pairs): hom(H,G)·n^{2e(H)} ≥ (2e(G))^{e(H)}·n^m. No division, no rounding; the maps-list hypotheses pin homCount to the true count of all vertex maps. Direction of the inequality matches the standard Sidorenko/reflection bound, and the tex states it explicitly.
- `mobiusAdj r` on Fin 2r — cycle plus opposite-vertex edges; `M8 : Graph 8 := mobiusAdj 4` (C8 + chords {i,i+4}), `actual_edge_counts : edgeCount M8 = 12 ∧ edgeCount K2 = 1`.
- `no_hom_to_K2 (f : Fin 8 → Fin 2) : ¬ Hom M8 K2 f` — symbolic for EVERY map (not just enumerated ones): the 5-cycle 0-1-2-3-4-0 forces alternation, impossible; enumeration scaffolding (`mapOf`/`codeOf`, `every_map_encoded : mapOf (codeOf f) = f`, `codeOf_mapOf`, `mapOf_injective`, `allMaps_complete`, `allMaps_nodup`) proves the 256 binary codes list all maps Fin 8 → Fin 2 exactly once.
- `actual_hom_count : homCount M8 K2 allMaps = 0`; `M8_not_Sidorenko : ¬ Sidorenko M8` (2^12·2^8 = 1048576 ≤ 0 is false).
- `def AllMobiusLaddersSidorenko : Prop := ∀ r, 2 ≤ r → ∀ H : Graph (2*r), (∀ i j, H.adj i j = mobiusAdj r i j) → Sidorenko H`; final `theorem conjecture_4396_false : ¬ AllMobiusLaddersSidorenko` at r = 4.

Mathematics: a non-bipartite H is never Sidorenko (witness G = K2: t(H,K2) = 0 < (1/2)^{e(H)}); M8 contains the 5-cycle 0-1-2-3-4-0, so hom(M8,K2) = 0 and the reflection bound fails. My independent computation confirms all counts. Interpretation calls disclosed: (i) "reflection bound" is read as the standard Sidorenko inequality t(H,G) ≥ t(K2,G)^{e(H)} — the canonical and only standard meaning of "Sidorenko graph", and the tex states the formulation it uses with a reference; (ii) the 8-vertex member is used so the counterexample is robust to conventions about whether the 4-vertex member (K4) belongs to the family — the report explicitly notes this and discloses the earlier withdrawn PR #318 by orionsheep that used K4; (iii) the odd-subdivision clause (a true known result) is untouched, but refuting the "all Möbius ladders" conjunct refutes the conjunction. Not vacuous: concrete graph, universal quantifier over all graphs G instantiated at K2, exact counts.
## Issues found
none blocking
## Verdict rationale
Clean build with standard axioms only; verify.py runs and matches its recorded outputs; my independently written enumeration reproduces every number (12 edges, 256 maps, 0 homomorphisms to K2, failed inequality 1048576 > 0). The Lean formalization encodes the standard Sidorenko property faithfully in exact integer arithmetic, and M8 — an unambiguous Möbius ladder containing a 5-cycle — decisively falsifies the conjecture's first conjunct.

## Disposition
APPROVED — merged into main (PR 354). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
