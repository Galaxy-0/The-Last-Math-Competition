# Solution Review — Conjecture 00000007400 (PR 381)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004031021`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — claims nonnegativity of super dimensions of supersymmetric representations (definition clause "Supersymmetric representations with super-dimension structure"; claimed proof method: supersymmetrization of characters).
- LaTeX: compiled (pdflatex twice, exit 0 both passes); shipped report.pdf is a real PDF (v1.5), extracted text matches report.tex.
- Lean build: exit 0, "[1727/1728] Built Main", "Build completed successfully.", zero warnings/errors; axiom audit lists only [propext, Classical.choice, Quot.sound] for `bracket_jacobi`, `even_dimension`, `odd_dimension`, `conjecture_7400_false`.
- Forbidden content: none. Only grep hit is VERIFICATION.md:18 English sentence "No sorry, admit, native_decide or new axiom declarations." No tactic-level `sorry`/`admit`, no `native_decide`, no `axiom` declarations, no `unsafe`/`extern`/`implemented_by`/`skipKernelTC`.
- Auxiliary code: none claimed ("No auxiliary code or computational assumptions required"). The mathematics is trivial and independently re-derived by hand: sdim = dim V₀̄ − dim V₁̄ = 0 − 1 = −1 < 0 for the purely odd line; both finranks (0 and 1) are also proved inside Lean, not assumed.
## Semantic audit
Conjecture (EN): "Conjecture: The nonnegativity of super dimensions holds, and the proof is the supersymmetrization of characters." (CN: "猜想：超维数的刚性：超维数的非负性且性的证明为特征标的超对称化"). The load-bearing claim is the universal statement sdim ≥ 0 for supersymmetric representations; the definition clause is generic ("super-dimension structure") and neither language version restricts the grading, excludes trivial actions, or requires a specific group/superalgebra — the report quotes and argues exactly this. Under every standard formalization of superdimension (dim of even part minus dim of odd part), a purely odd representation has sdim = −dim < 0, so the claim is false in any model containing the parity-reversed trivial module.

Lean encodings:
- `structure SuperSpace (V) [AddCommGroup V] [Module ℂ V]` with `even odd : Submodule ℂ V`, `disjoint : Disjoint even odd`, `exhaustive : even ⊔ odd = ⊤` — a genuine direct grading by actual complex subspaces (not asserted dimension data).
- `superDimension S = (finrank ℂ S.even : ℤ) - (finrank ℂ S.odd : ℤ)` — the standard sdim as an integer.
- Lie superalgebra: ℂ purely even with `def bracket : ℂ →ₗ[ℂ] ℂ →ₗ[ℂ] ℂ := 0`, with `bracket_skew` and `bracket_jacobi` proved (trivially, as everything vanishes).
- `structure SuperRepresentation` — a `SuperSpace` plus a bilinear action `ℂ →ₗ[ℂ] V →ₗ[ℂ] V`, the commutator identity `action (bracket a b) v = action a (action b v) - action b (action a v)` (the super-commutator identity for a purely even algebra), and parity preservation of both halves.
- Witness: `oddLine : SuperRepresentation ℂ` with `even := ⊥`, `odd := ⊤`, zero action; all structure fields discharged by proof.
- `theorem even_dimension : finrank ℂ oddLineSpace.even = 0` and `theorem odd_dimension : finrank ℂ oddLineSpace.odd = 1` via `finrank_bot` / `finrank_top`+`Module.finrank_self`.
- `theorem actual_super_dimension : superDimension oddLine.space = -1`.
- `theorem conjecture_7400_false : ¬ (∀ R : SuperRepresentation ℂ, 0 ≤ superDimension R.space)` — witness-applied negation of the literal nonnegativity claim.

(i) Faithful: yes — the grading is a real direct decomposition, the action is bilinear with the super representation identity, and sdim is the standard difference of proved finranks. (ii) Hypotheses: none beyond the structure laws, all verified for the witness. (iii) −1 < 0 contradicts nonnegativity. (iv) Non-vacuous: `oddLine` is an explicitly constructed instance. Rigor bar: this is NOT a numeric-facts-only proof — the graded module, the representation laws, and both dimensions are constructed/proved in Lean; the final theorem negates a genuine universally quantified claim over a class (fixed algebra = 1-dim abelian purely even; V = ℂ) that is a subdomain of the unrestricted original, so a counterexample there refutes the original (report states this containment argument, correctly). The trivial-action/abelian-algebra choice is the weakest-point counterexample; under the repo precedent that the literal bilingual text is authoritative and carries no restriction excluding it, it stands. The supercharacter angle (supersymmetrization "proof" clause) is addressed in the report: the supertrace of the identity on a purely odd space is −1, so character symmetrization cannot rescue nonnegativity.
## Issues found
none blocking
(Note for the record: the counterexample is deliberately minimal — trivial action of the trivial Lie superalgebra on the odd line. The conjecture text imposes no faithfulness/positivity restriction, so this is a valid falsifier; flagged only because it is an edge-case-class witness.)
## Verdict rationale
Nonnegativity of superdimensions is genuinely false in every standard sense (the odd line is the canonical obstruction), and the submission formalizes the full object — direct complex grading, bilinear action with the super-commutator law, parity preservation — computing sdim = −1 in Lean from proved finranks with only standard axioms. Build, PDF, and content audits are clean, and the report honestly states the restricted-class containment argument. The witness is trivial by design but the bilingual statement contains no restriction that would exclude it.

## Disposition
APPROVED — merged into main (PR 381). Independent fresh rebuild of the Lean project (exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
