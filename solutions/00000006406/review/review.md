# Solution Review — Conjecture 00000006406 (PR 384)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004031852`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the complement operation is always an isometry of the (symmetric-)difference metric, the composition of complements is an involution, the isometry verification being the De Morgan identity (EN+CN identical in scope).
- LaTeX: recompiled in /tmp/tlmc-review5/scratch/pr-384 with pdflatex twice, exit 0, zero errors/undefined references; shipped report.pdf is a genuine PDF (24,681 bytes, tectonic) whose embedded title text "Complement is an isometric involution / Proof of Conjecture 00000006406" matches report.tex; full report read — it states and proves A^c∖B^c = B∖A, A^c△B^c = A△B, distance preservation for any size functional W, involution and C∘C = id, and the De Morgan route.
- Lean build: `lake build` exit 0 ("Build completed successfully", 1188 targets; environment pre-built cache lacked some oleans so ~440 Mathlib modules were compiled from source — all succeeded). Zero warnings. `#print axioms` for all four audited theorems: [propext, Classical.choice, Quot.sound] only.
- Forbidden content: grep for `sorry`, `admit`, `native_decide`, `axiom `, `unsafe`, `implemented_by`, `extern`, `skipKernelTC` over Main.lean — no matches; no `set_option` of any kind; no custom axioms.
- Auxiliary code: none shipped and none needed (purely symbolic proof); my own independent Python check: 2000 random trials confirmed A^c△B^c = A△B as SETS (hence equal cardinalities) and double-complement involution — matches the Lean identity `complement_symmetric_difference`.
## Semantic audit
Conjecture (literal): "The complement operation is always an isometry of the difference metric and the composition of complements is an involution, the verification of the isometry being the De Morgan identity."

Lean coverage (all in `namespace ComplementIsometry`, Main.lean):
- `theorem complement_symmetric_difference {α : Type*} (A B : Set α) : Aᶜ ∆ Bᶜ = A ∆ B` — the core identity, fully general (arbitrary universe, arbitrary set pair). Since the symmetric-difference SETS are literally equal, every size functional (cardinality, measure, any `weight : Set α → β`) yields equal distances: `difference_distance_preserved (weight : Set α → β) (A B : Set α) : differenceDistance weight Aᶜ Bᶜ = differenceDistance weight A B`, unconditional.
- `theorem complement_isometry {α} [PseudoMetricSpace (Set α)] (weight : Set α → ℝ) (h_distance : ∀ A B, dist A B = differenceDistance weight A B) : Isometry (fun A : Set α => Aᶜ)` — the only structural hypothesis is that `dist` IS the difference metric, i.e. the conjecture's own object; it does NOT assume complement preserves dist (no circularity/strengthening). Non-vacuity is proved in-file: `theorem concrete_hamming_isometry (ι : Type*) [Fintype ι] : Isometry (complementWord (ι := ι))` — the canonical finite powerset with counting (Hamming) distance, unconditionally. Supporting lemmas `word_complement_is_set_complement` and `word_mismatch_is_symmetric_difference` prove the words-are-sets correspondence.
- Involution, both readings: `complement_involutive (α) : Function.Involutive (fun A : Set α => Aᶜ)`, `composed_complement_is_identity : (complement) ∘ (complement) = id`, `composed_complement_involutive : Function.Involutive ((complement) ∘ (complement))` — covers both the standard reading (C involutive) and the hyper-literal reading (the composition C∘C is an involution).
- De Morgan: `deMorgan_union`, `deMorgan_intersection` proved pointwise and included in the final conjunction.
- Final theorem `conjecture_6406` = Isometry ∧ Involutive C ∧ Involutive (C∘C) ∧ (∀ A B, both De Morgan identities) — the full statement, universally quantified over all set pairs.

Hypotheses satisfied: yes (difference metric hypothesis is definitional; Hamming instance unconditional). The theorem establishes the conjecture (proof claim). Not vacuous; no strengthened hypotheses; no edge-case/degenerate reading needed. The restriction "on a restricted family complement needs a complement-closed family" is honestly discussed in the report and VERIFICATION.md; the Lean works on the full powerset Set α, which is the conjecture's setting.
## Issues found
- Minor (non-blocking): no statement.md file in this submission (present in the other two); the conjecture is instead quoted in VERIFICATION.md and addressed in report.tex. Repo rules require LaTeX source + PDF + Lean project only, so this is cosmetic.
- Minor (non-blocking): README "Reproduce" suggests `lake update` / `lake exe cache get`, which is not needed with the pinned manifest; build verified directly.
## Verdict rationale
The Lean project proves the exact set identity Aᶜ△Bᶜ = A△B for arbitrary sets, derives from it preservation of every symmetric-difference-based distance for any weight functional, upgrades it to a genuine Mathlib `Isometry` under exactly the definitional hypothesis "dist is the difference metric" (with an unconditional concrete Hamming instance proving non-vacuity), and proves the involution claims under both readings plus the De Morgan identities. The build is clean with only standard axioms, the LaTeX compiles and matches the shipped PDF, and my independent computation confirms the identity. The full conjectured statement is established.

## Disposition
APPROVED — merged into main (PR 384). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
