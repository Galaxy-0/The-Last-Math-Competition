# Solution Review — Conjecture 00000008842 (PR 390)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004034655`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The domain of a maximal monotone operator is always dense in its closure; and the graph of the operator is a maximally monotone closed set in the product space." NOTE: this is a PROOF (report: "Proof of Conjecture 00000008842"), not a disproof.
- LaTeX: pdflatex compiled twice, exit 0; shipped 1-page report.pdf genuine; text identical to my rebuild modulo Tectonic-vs-pdflatex glyph-encoding artifacts (braces/semicolons/subscript positioning).
- Lean build: exit 0 (1811/1812 Built Main). No warnings. Six `#print axioms` lines (closed, denseRange_closureInclusion, maximal_membership, maximal_graph_closed, both conjecture_8842 instances) = exactly [propext, Classical.choice, Quot.sound].
- Forbidden content: grep over Main.lean + lakefile.lean: no hits.
- Auxiliary code: none beyond Lean; VERIFICATION.md claims re-confirmed (build exit 0, axiom sets, clean grep, PDF renders; toolchain 4.19.0, Mathlib c44e0c8e…).
## Semantic audit
Clause 1 (literal): "domain … always dense in its closure" — formalized as `theorem denseRange_closureInclusion (s : Set X) : DenseRange (closureInclusion s)` where `closureInclusion s : s → closure s` is the canonical inclusion. This is the literal claim: D dense in closure(D) — a topological tautology, honestly proven for every set (not vacuous as a theorem; it instantiates the conjecture clause exactly, and the report transparently notes it is relative density in the closure, "including when the domain is empty"). The tautological character is a property of the conjecture's wording, not of the submission; per repo precedent the literal statement is authoritative.
Clause 2: "graph … is a maximally monotone closed set in the product space" — the substantive half. General lemma: `theorem closed (hrefl) (hsymm) (hsection : ∀ q, IsClosed {p | C p q}) (hG : Maximal C G) : IsClosed G` via `G = ⋂ q ∈ G, {p | C p q}` and the one-point-extension membership lemma — correct mathematics. Instantiated twice with genuine pairings:
- Inner-product: `PairMonotone p q := 0 ≤ inner (p.1−q.1) (p.2−q.2)` on E × E (real inner-product space; `pair_symm` proven; sections closed by continuity of inner). `theorem conjecture_8842 (A : E → Set E) (hA : MaximalMonotoneGraph (Graph A)) : DenseRange (closureInclusion (Domain A)) ∧ MaximalMonotoneGraph (Graph A) ∧ IsClosed (Graph A)`.
- Continuous-dual: `PairMonotone p q := 0 ≤ (p.2 − q.2) (p.1 − q.1)` with target `E →L[ℝ] ℝ`, `section_closed` by continuity of `clm_apply`; `DualMonotoneProof.conjecture_8842` analogous.
Maximality is defined by absence of a proper monotone graph extension (no closedness assumed); closedness in the product norm topology is DERIVED. The hypothesis hA is exactly "A is a maximal monotone operator"; re-asserting graph maximality in the conclusion is definitional, and the closedness component is the proven, nontrivial part. The closedness argument (maximal monotone graph is closed since it equals the intersection of its closed monotone-compatibility sections) is the standard correct proof. Not vacuous: maximal monotone operators exist; the implication carries real content.
## Issues found
none blocking. (Informational: clause 1 is tautological as literally worded — any set is dense in its own closure — and the submission proves it as such; coordinator may want to be aware that this conjecture's first clause is trivially true under the literal authoritative reading.)
## Verdict rationale
Everything compiles, builds, and audits cleanly with only the three standard axioms. The formalization uses the genuine monotonicity definitions in both the Hilbert and continuous-dual settings, proves the closedness clause by the classical intersection-of-closed-sections argument, and proves the density clause literally as stated. Faithful and complete.

## Disposition
APPROVED — merged into main (PR 390). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
