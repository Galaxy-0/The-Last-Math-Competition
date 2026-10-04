# Solution Review — Conjecture 00000008844 (PR 387)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004033703`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "Resolvent operators are always firmly nonexpansive; and their fixed point set is exactly the zero set of the monotone operator." NOTE: this submission is a PROOF (the conjecture is true in the standard reading), not a disproof — the report title says "Proof of Conjecture 00000008844".
- LaTeX: compiled with pdflatex twice, exit 0 both passes; shipped report.pdf is a genuine 1-page PDF rendering identical content (only ligature-extraction artifacts vs my pdflatex build).
- Lean build: exit 0 ("Build completed successfully", 1662 jobs). No warnings. `#print axioms` for `firm_graph`, `graph_iff_value`, `resolvent_firm`, `fixed_set_eq_zero_set` = exactly [propext, Classical.choice, Quot.sound].
- Forbidden content: grep over Main.lean + lakefile.lean (sorry/admit/native_decide/`axiom `/unsafe/implemented_by/extern/skipKernelTC): no hits.
- Auxiliary code: none beyond Lean; VERIFICATION.md claims (build, axioms, clean grep, PDF) independently re-confirmed. Mathlib pinned c44e0c8e…, Lean 4.19.0.
## Semantic audit
Conjecture (EN/CN consistent): 预解算子恒 Firm 非扩张；且其不动点集恰为单调算子的零点集. Formalization over an arbitrary real inner-product space `E` (Hilbert spaces included; completeness honestly noted as unnecessary):
- `def MonotoneGraph (A : E → Set E) : Prop := ∀ u v a b, a ∈ A u → b ∈ A v → 0 ≤ inner (u - v) (a - b)` — exact standard set-valued monotonicity.
- `def Resolves A λ x u := ∃ a ∈ A u, x = u + λ • a` (x ∈ (I+λA)u), `Domain A λ = ran(I+λA)` — the natural resolvent domain.
- `theorem firm_graph : ‖u - v‖^2 ≤ inner (u - v) (x - y)` for u,v resolving x,y — the core monotonicity computation ⟨u−v, x−y⟩ = ‖u−v‖² + λ⟨u−v, a−b⟩ ≥ ‖u−v‖², valid for λ ≥ 0.
- `theorem unique_value` — single-valuedness on the domain (x=y forces ‖u−v‖=0); resolvent map then built by choice with `graph_iff_value` proving the map's value relation is exactly the inverse graph.
- `theorem resolvent_firm (x y : Domain A lambda) : ‖resolvent A lambda x - resolvent A lambda y‖^2 ≤ inner (resolvent … x - resolvent … y) (x.val - y.val)` — the standard firm-nonexpansiveness inequality, on the full natural domain.
- `theorem fixed_set_eq_zero_set : FixedSet A lambda = ZeroSet A` with `diagonal_iff_zero : Resolves A lambda x x ↔ (0:E) ∈ A x` — exact set identity; both directions proven (zeros lie in the domain automatically; uniqueness gives the fixed-point property).
Faithfulness: "always firmly nonexpansive" is proven for every monotone A and λ ≥ 0 (>0 for the fixed-point clause), which matches the universal quantifier; the only interpretive choice is that the resolvent is treated on its natural domain ran(I+λA), which is the standard definition of (I+λA)⁻¹ for a merely monotone operator (totality would require maximality, which the conjecture does not grant; the report explicitly discloses this, with the {(0,0)}-graph example). The firm nonexpansiveness inequality proved is the standard definition, not a weakening. Not vacuous: monotone operators exist, the inequality has content, and the set identity instantiates nontrivially.
## Issues found
none blocking. (Flag for awareness: this PR proves the conjecture rather than disproving it — appropriate, since the conjecture is classically true; no trickery detected.)
## Verdict rationale
The Lean development is complete (no sorry/axioms beyond the standard three), builds cleanly, and establishes both conjuncts of the conjecture in full generality over real inner-product spaces with the standard definitions. The report is a faithful, honest account including the domain subtlety. Both the mathematics (resolvents of monotone operators are firmly nonexpansive on ran(I+λA); Fix(J_λ) = zer(A) for λ>0) and its formalization check out.

## Disposition
APPROVED — merged into main (PR 387). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
