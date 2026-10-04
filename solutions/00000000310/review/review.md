# Solution Review — Conjecture 00000000310 (PR 396)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004040724`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "Bad^abs = {x ∈ R² : uniformly over all unit vectors e ∈ S¹, ∃ c(e) > 0 with ‖q(e·x)‖ > c(e)/q} has Hausdorff dimension 2 and is absolute winning" (disproof submission; first submission by NEW solver C0ldSmi1e — full first-time scrutiny applied).
- LaTeX: pdflatex twice, exit 0 both passes, 0 errors; shipped main.pdf is a genuine 3-page PDF matching main.tex (title/abstract/theorem content verified by text extraction; recompile also 3 pages).
- Lean build: `lake build` exit 0 ("Build completed successfully"); `lake env lean -DwarningAsError=true Conjecture310.lean` exit 0; `lake env lean Check.lean` exit 0 printing all seven axiom audits — every theorem depends only on [propext, Classical.choice, Quot.sound]. lakefile.toml correctly declares `[[lean_lib]] name = "Conjecture310"` with `defaultTargets = ["Conjecture310"]`, so the default build genuinely compiles the proof module.
- Forbidden content: grep over lean/Conjecture310.lean, Check.lean, lakefile.toml for sorry/admit/native_decide/axiom decls/unsafe/implemented_by/extern/skipKernelTC — no hits. No `set_option debug.skipKernelTC`.
- Auxiliary code: no scripts needed (universal geometric argument); verification.txt fully cross-checked: all ten SHA-256 artifact hashes re-computed and MATCH exactly; conjecture.md is byte-identical (diff) to the official conjectures/00000000310.md; recorded build/audit commands and outputs match my independent reproduction line for line.
- First-time-solver material checks: folder name `C0ldSmi1e_submission_20261004040724` matches [GitHub_ID]_submission_<14-digit timestamp>; provenance transparently disclosed ("Prepared with Codex assistance"); SEMANTIC_REVIEW.md honestly labeled as non-official internal cross-check; README reproduction commands work as documented (modulo cache commands not needed here since Mathlib is pre-populated).
## Semantic audit
Conjecture literal claim (EN): "Bad^abs consists of those x ∈ R² for which, uniformly over all unit vectors e ∈ S¹, there exists c(e) > 0 with ‖q(e·x)‖ > c(e)/q. Conjecture: Bad^abs has Hausdorff dimension 2 (full), and it is absolute winning..." (CN identical: 对一切单位向量 e∈S¹ — "for ALL unit vectors", no exclusion of any direction.)

Lean encodings (namespace `Conjecture310`, ambient `abbrev Plane := EuclideanSpace ℝ (Fin 2)` — the genuine Euclidean plane, not a sup-norm substitute):
- `def distanceToIntegers (t : ℝ) : ℝ := Metric.infDist t (Set.range (Int.cast : ℤ → ℝ))` — nearest-integer distance, standard reading of ‖·‖ in Diophantine approximation; `distanceToIntegers_zero : distanceToIntegers 0 = 0`.
- `def BadAbs : Set Plane := {x | ∀ e : Plane, ‖e‖ = 1 → ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 0 < q → c / (q:ℝ) < distanceToIntegers ((q:ℝ) * ⟪e, x⟫_ℝ)}` — faithful to the literal definition under the WEAKER direction-dependent-constant reading; emptiness under the weaker reading a fortiori refutes the stronger uniform-constant reading.

Key theorems:
- `theorem perpendicular_unit (x : Plane) : ∃ e : Plane, ‖e‖ = 1 ∧ ⟪e, x⟫_ℝ = 0` — genuine construction (e = ‖(−x₁,x₀)‖⁻¹(−x₁,x₀) for x ≠ 0; (1,0) for x = 0), proved from the Euclidean norm/inner product.
- `theorem badAbs_eq_empty : BadAbs = ∅` — applies the defining membership at the perpendicular unit direction and denominator q = 1: c/1 < distanceToIntegers(⟪e,x⟫) = 0 contradicts c > 0. Genuine kernel-checked contradiction.
- `theorem dimH_badAbs_eq_zero : dimH BadAbs = 0` (via Mathlib's `dimH_empty`) and `theorem dimH_badAbs_ne_two : dimH BadAbs ≠ 2` — direct negation of the conjecture's dimension conjunct using Mathlib's genuine `dimH`, no surrogate notion.
- Bonuses: `badAbs_inter_eq_empty`/`dimH_badAbs_inter_eq_zero` — the intersection-with-full-dimensional-Cantor clause also fails (intersection is empty, dimension 0).

Readings robustness: the obstruction (q·0 = 0 ⇒ distance 0 > c/q impossible) holds for every positive denominator, so eventual-denominator or infinitely-many-denominator variants fail identically; non-strict bounds fail; absolute-value reading of ‖·‖ fails; uniform constant fails a fortiori. The absolute-winning clause is not formalized, which is fine — one false conjunct (dim = 2) suffices, and additionally the empty set cannot be absolute winning or have full-dimensional intersections.

Mathematical verdict: the literal statement's own definition quantifies over all unit directions including the one perpendicular to x, where e·x = 0 identically; hence Bad^abs = ∅ and dim_H = 0 ≠ 2. The disproof is airtight under the literal bilingual statement.
## Issues found
Degenerate-flavor flag (for coordinator attention, non-blocking): the disproof works by showing the conjecture's own definition trivializes to the empty set (perpendicular-direction obstruction) rather than by engaging the deep intended literature notion (where such a definition would need direction restrictions). Under the repo precedent that the literal bilingual statement is authoritative and that the text carries NO restriction on the directions (一切单位向量/all unit vectors), this is a valid disproof. The report handles interpretation honestly and transparently (weaker-reading argument, robustness discussion, exact quote of the source).
## Verdict rationale
This first-time submission is materially complete and honest: the Lean project genuinely builds the proof module with zero warnings-as-errors, all theorems rest on standard axioms only, every recorded hash and claim in verification.txt reproduces exactly, the bundled conjecture copy is byte-identical to the official one, and the LaTeX/PDF are genuine and matching. The mathematical argument correctly derives Bad^abs = ∅ from the literal all-directions definition, refuting the dimension-2 conjunct (and, via the intersection lemmas, the winning/intersection clause as well). Approved, with the trivialized-definition nature flagged for the coordinator.

## Disposition
APPROVED — merged into main (PR 396). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
