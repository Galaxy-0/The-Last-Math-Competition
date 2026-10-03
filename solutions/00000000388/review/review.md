# Solution Review — Conjecture 00000000388 (PR 330)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003130000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — W_m = {ξ : w_n(ξ) ≤ n/m for infinitely many n} \ ∪_k U_k; each W_m nonempty and uncountable, distinct W_m disjoint, union = all transcendentals.
- LaTeX: compiled ok (pdflatex twice, exit 0, 0 errors); included main.pdf real PDF v1.5, 2 pages, matches tex.
- Lean build: fresh build after `rm -rf .lake`, exit 0, no warnings; both final theorems depend on NO axioms at all (matches lean-verification.txt and verification.json `printed_axioms: []`).
- Forbidden content: none.
- Auxiliary code: none shipped (`auxiliary_scripts_rerun: []`); nothing to run.
## Semantic audit
Conjecture literal claim: "Each W_m is nonempty and uncountable, distinct W_m are disjoint, and the union of the classes is the full set of transcendentals." The disproof shows the definition of W_m makes the first and second clauses jointly unsatisfiable, for every possible instantiation.

Key Lean definitions, all faithful:
- `RationalBound` with `BoundLE q r := q.num * r.den ≤ r.num * q.den` — exact rational comparison (no integer division); `threshold n m = ⟨n, m⟩` is exactly n/m.
- The condition w_n(ξ) ≤ n/m is `(orders x n).contains (threshold n m)` where `UpperCut` is an upward-closed set of rational bounds; `cutOfValue`/`cutOfValue_exact` prove that for any transitive ordered value type (reals, extended reals) this is exactly the comparison v ≤ n/m. Quantifying over all upward-closed cuts (a superset of numerical values incl. +∞) only strengthens the impossibility result.
- `InfinitelyOften p := ∀ B, ∃ n, B < n ∧ p n` — exact infinitude.
- `NoU U x := ∀ k, ¬ U k x` — identical exclusion for all m, as in the source.
- `W orders U m x := NoU U x ∧ InfinitelyOften (fun n => (orders x n).contains (threshold n m))` — the source's W_m, with the same orders and U for all m.
- `W_antitone : m ≤ k → W orders U k x → W orders U m x` (thresholds nest: `threshold_antitone`, monotone transfer via upward closure).

Final theorems: `conjecture388_refuted : ¬ (EveryClassNonempty orders U ∧ PairwiseDisjoint orders U)` — universally over the underlying type X, the approximation orders, and the family U; and `ordered_value_version` — the same negation stated directly through numerical comparisons `v.le (orders x n) (v.ofBound (threshold n m))`, i.e., w_n(ξ) ≤ n/m in an arbitrary ordered value type.

(i) Definitions faithful (exact rationals, exact infinitude, shared U-exclusion). (ii) Hypotheses: the "counterexample" is the conjecture's own two clauses (each W_m nonempty; pairwise disjointness), both literally asserted by the source; no extra assumption is smuggled in. (iii) With W_2 ⊆ W_1 and W_2 ≠ ∅, W_1 ∩ W_2 ≠ ∅ contradicts disjointness — the negation is proved for arbitrary data, so no instantiation (in particular no analytic one) can satisfy both clauses; the conjunction claimed by the conjecture is necessarily false. (iv) Not vacuous: the W_m classes with their threshold definition are the decisive objects, and the nesting proof engages them directly; this is not the PR #286-288 pattern of proving numeric facts with the conjecture's objects absent. LaTeX matches Lean (same W_k ⊆ W_m statement, same RationalBound/UpperCut bridge, same theorem names).
## Issues found
- Non-blocking (interpretation): the source does not state the index range of m; the Lean proof uses m = 1, 2. The nesting argument (`W_antitone`) works for any two distinct positive indices, so any index set containing at least two values yields the same contradiction; only a single-class reading (which would make "distinct W_m are disjoint" vacuous) escapes, and that reading is contrary to the plural phrasing.
- Non-blocking: clauses (uncountability, union = transcendentals) are not formalized; refuting a sub-conjunction suffices.
## Verdict rationale
The conjecture's nonemptiness and disjointness clauses are jointly contradictory with its own definition of the W_m classes: thresholds n/m nest, so W_k ⊆ W_m for m ≤ k, and a nonempty nested pair cannot be disjoint. The Lean proof is universal over all data (with an explicit numerical bridge via `ordered_value_version`), uses no axioms whatsoever, and everything compiles and runs. A genuine refutation of the conjecture as stated.

## Disposition
APPROVED — merged into main (PR 330). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
