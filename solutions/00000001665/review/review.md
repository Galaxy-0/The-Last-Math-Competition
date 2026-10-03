# Solution Review — Conjecture 00000001665 (PR 305)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — b(G) ≤ ⌈√n⌉+1 (paths attain ⌈√n⌉); tight examples characterized as Cartesian products of the Petersen graph with paths having burning number exactly ⌈√n⌉+1, with no higher-order tight family.
- LaTeX: compiled ok (pdflatex twice, exit 0, 1 page, 131 KB); included main.pdf is a real PDF (1 page, verified by stream decompression); tex and pdf agree.
- Lean build: fresh build after `rm -rf .lake`, exit 0, no warnings (warnings-as-errors active), v4.19.0, imports only Std.
- Forbidden content: none — no sorry/admit/native_decide/axiom/unsafe/implemented_by/extern; only maxRecDepth/maxHeartbeats options (allowed). `#print axioms not_tight_family_claim` = [propext] only.
- Auxiliary code: no auxiliary scripts present (verification.json records `auxiliary_scripts_rerun: []`, consistent with the submission contents). All recorded sha256 file hashes match current files; official conjecture sha256 = original_source_sha256. I ran my own independent Python cross-check: graph is 4-regular on 20 vertices; the tex's burned sets B1={0}, B2={0,1,4,5,10}, B3={0..11,14,15}, B4=all-20 reproduce exactly; a single-source standard burning also finishes in 4 rounds; diameter 3; every |Ball(s,2)|=14 so max 3-round coverage 19<20, hence b=4 exactly.
## Semantic audit
Conjecture (literal): "Cartesian products of the Petersen graph with paths have burning number ⌈√n⌉+1" (the tight-family clause; the conjecture is a conjunction of the upper bound, this characterization, and "no higher-order tight family").

Lean objects: `petersen u v` is the standard Petersen graph on 0..9 (outer 5-cycle (u+1)%5, inner pentagram (u−5)+2 mod 5, spokes u%5 = v%5 across the halves) — the standard model. `petPath m` on Fin(10m) is exactly the Cartesian product with the m-vertex path: same layer + Petersen edge, or same Petersen coordinate + adjacent layers. This is certified, not assumed: `product_encoding` proves the product adjacency through the explicit bijorphism `encode u j = u+10j` (proved bijective by real arithmetic, not decide), and `graph_simple` proves irreflexivity+symmetry by kernel decide.

Burning semantics: `advance` = keep burned ∪ ignite source ∪ spread old fires one edge (the update rule displayed in the tex); `legal` = each source unburned at the beginning of its round; `BurnsIn adj k` = ∃ source list of length ≤ k, legal, with all vertices burned at the end; `BurningNumberIs adj b` = BurnsIn b ∧ ∀k<b, ¬BurnsIn k — i.e. b is exactly the burning number (achievability + minimality). This matches the conjecture's definition "minimal number of rounds needed to burn all vertices progressively". Note the round order is ignite-then-spread rather than the common spread-then-ignite; this is at least as permissive, but soundness of the certificate is unaffected: the end-state is the ball-covering ∪ᵢ Ball(sᵢ, k−i), any such covering yields a standard-legal burning in k rounds, and my independent check confirms a plain single-source standard burning finishes in 4 rounds.

Final theorems: `burns_in_four : BurnsIn (petPath 2) 4` (kernel decide on the explicit sources [0,1,2,12], with `legal_sources` and `all_burned`), `ceil_sqrt_twenty : CeilSqrtIs 20 5` where `CeilSqrtIs n r := (r−1)² < n ∧ n ≤ r²` is the correct integer characterization of r = ⌈√n⌉, and
`not_tight_family_claim : ¬TightFamilyClaim` where `TightFamilyClaim := ∀ m r, 0 < m → CeilSqrtIs (10*m) r → BurningNumberIs (petPath m) (r+1)`.
The refutation instantiates m=2, r=5: the conjectured exact value 6 is contradicted by BurnsIn 4 with 4 < 6. Logically, since BurningNumberIs (petPath 2) 6 requires ¬BurnsIn 4 but BurnsIn 4 holds, the universally quantified tight-family clause is false — the Petersen □ P2 product (n=20, ⌈√20⌉+1 = 6) has burning number 4 ≠ 6. The counterexample is in the conjecture's family (P2 is a path; petPath 2 is the genuine Cartesian product), engages the actual objects, and is not vacuous. The separate universal bound b ≤ ⌈√n⌉+1 is explicitly not asserted — correct, since 4 ≤ 6 does not contradict it; the conjecture as a whole fails via its tight-family characterization clause.

LaTeX/Lean match: same graph model, same sources [0,1,2,12], same burned sets, same numbers 4 < 6 = ⌈√20⌉+1, same theorem names.
## Issues found
- Minor (non-blocking): the burning round order (ignite-then-spread, legality at round start) differs from the common spread-then-ignite convention; as analyzed, this does not affect the truth of the upper-bound certificate, and the actual b=4 is confirmed independently under the strict convention.
- Minor (non-blocking): only the tight-family clause is refuted, not the universal upper bound; this is correctly scoped in SOURCE.md/main.tex and suffices to refute the stated conjunction.
- Minor (non-blocking): a graph-theoretic check that "petPath m" for m=1 degenerates to the Petersen graph itself (also a refuting member) is not needed since m=2 is used.
## Verdict rationale
The submission compiles and runs cleanly with no placeholders, the Lean definitions faithfully encode the Petersen graph, its Cartesian product with a path, and progressive burning, and the final theorem negates exactly the conjecture's tight-family claim: Petersen □ P2 has burning number 4, not the conjectured ⌈√20⌉+1 = 6. My independent computation confirms b = 4 exactly. This is a genuine disproof of the conjecture as stated.

## Disposition
APPROVED — merged into main (PR 305). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
