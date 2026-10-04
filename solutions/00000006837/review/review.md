# Solution Review — Conjecture 00000006837 (PR 403)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004043918`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The invariant subspaces of the adjoint hold, the combination of the subspaces being orthogonal complements" (adjoint invariant subspaces paired by orthogonal complement)
- LaTeX: report.tex recompiled in /tmp/tlmc-review5/scratch/pr-403 with pdflatex (2 passes), exit 0, 0 errors, 1 page; shipped report.pdf is a real PDF 1.5, 26695 bytes, whose embedded text matches report.tex content (⟨x,A*y⟩=⟨Ax,y⟩, U⊥ definition, RCLike, bijection statements)
- Lean build: exit 0 ("Build completed successfully", 2085 jobs, pre-populated cache); only output is 4 `#print axioms` info lines, each showing exactly [propext, Classical.choice, Quot.sound]
- Forbidden content: grep over own .lean files (Main.lean only) for sorry/admit/native_decide/`axiom `/unsafe/implemented_by/extern/skipKernelTC: no hits; no `#eval`, no `decide`-style shortcuts; single import Mathlib.Analysis.InnerProductSpace.Adjoint
- Auxiliary code: none shipped (no scripts); README reproduction steps run manually: `lake build` exit 0, `lake env lean Main.lean` recompiles clean
## Semantic audit
Conjecture (EN): "The invariant subspaces of the adjoint hold, the combination of the subspaces being orthogonal complements." CN similarly: 伴随的不变子空间且间的组合为正交补. The standard, and only sensible, mathematical reading: invariant subspaces of an operator A correspond to invariant subspaces of its adjoint A* via orthogonal complementation.

The Lean encodes this with genuine Mathlib objects:
- `variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]` — real AND complex Hilbert spaces, arbitrary dimension, exactly the bounded-adjoint setting.
- `def Invariant (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop := ∀ x ∈ U, A x ∈ U` — the actual preservation condition.
- `theorem orthogonal_invariant (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (h : Invariant A U) : Invariant (ContinuousLinearMap.adjoint A) Uᗮ` — forward direction proved from `ContinuousLinearMap.adjoint_inner_right`, valid for EVERY subspace (no closedness), so no quietly strengthened hypothesis here.
- `theorem closed_invariant_iff ... (h : IsClosed (U : Set E)) : Invariant A U ↔ Invariant (ContinuousLinearMap.adjoint A) Uᗮ` — full equivalence; closedness is unavoidable (for a dense non-closed U, Uᗮ = ⊥ is trivially invariant while U need not be), and the report/VERIFICATION state this explicitly rather than hiding it.
- `def adjointCorrespondence (A : E →L[𝕜] E) : ClosedInvariant A ≃ ClosedInvariant (ContinuousLinearMap.adjoint A)` — an actual Equiv with both inverse laws proved via `Submodule.orthogonal_orthogonal_eq_closure`; this IS the "combination of the subspaces being orthogonal complements".
- `theorem correspondence_reverses_order ... : U.val ≤ V.val ↔ (adjointCorrespondence A V).val ≤ (adjointCorrespondence A U).val` — order-reversal, the lattice content of the claim.

Hypotheses satisfied: only [RCLike 𝕜] + completeness, i.e., exactly a Hilbert space; `E →L[𝕜] E` is a bounded (continuous) linear operator. Not vacuous: the theorem quantifies over all A and all U; instantiating A = id or U = ⊤ gives non-trivial content, and the equivalence is between two infinite lattices. The forward implication — the literal conjecture claim that the adjoint's invariant subspaces are the orthogonal complements — is established unconditionally for every subspace; the converse restriction to closed subspaces is the mathematically correct maximal statement and is disclosed in report.tex §"Precise statement" and VERIFICATION.md.
## Issues found
none blocking. (Minor note: the conjecture text itself is garbled; submission adopts the standard textbook theorem, which is the only coherent reading, and proves its strongest true form.)
## Verdict rationale
The Lean project builds cleanly with only the three standard logical axioms, uses genuine Mathlib adjoints and orthogonal complements over real or complex Hilbert spaces in arbitrary dimension, and establishes the adjoint/orthogonal-complement correspondence in full: forward for all subspaces, equivalence and order-reversing bijection for closed subspaces (the necessary and standard restriction, explicitly disclosed). The LaTeX compiles and the shipped PDF matches. The proof is complete, non-vacuous, and faithful to the only sensible bilingual reading of the conjecture.

## Disposition
APPROVED — merged into main (PR 403). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
