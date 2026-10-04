# Solution Review — Conjecture 00000006330 (PR 356)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — there exist two matrices with the same determinant and permanent but different integrality types, realized by an explicit pair that is not related by unimodular row transformations (a claimed PROOF submission).
- LaTeX: recompiled in /tmp/tlmc-review2/scratch/pr-356, pdflatex twice exit 0; shipped main.pdf text 99.7% identical to recompiled (differences are pure glyph-extraction artifacts: delimiters, underscores); ALL 17 files' SHA-256 match VALIDATION.json byte-for-byte.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (warningAsError=true); only info output is `#print axioms`: `conjecture_6330` depends on `[propext, Quot.sound]` only — exactly the standard axioms claimed in the tex. Toolchain lean4:v4.19.0, bundled Std only.
- Forbidden content: grep for sorry/admit/native_decide/axiom-decls/unsafe/implemented_by/extern/skipKernelTC — no matches. `decide` is used only for closed concrete computations over Fin 2 → Fin 2 → Int (kernel-checked, legitimate).
- Auxiliary code: no scripts shipped (none needed — the object is 2×2 integer matrices; every numeric fact is decided inside Lean's kernel). I independently re-derived with python3: det A = det B = 4, per A = per B = 4; brute force over all unimodular U, V with entries in [-6,6] finds NO U B = A, U A = B, U B V = A, U A V = B; Smith normal forms (1,4) vs (2,2) as claimed. The algebraic obstructions in the paper (2 | entries of U·B so U·B ≠ A; (U·A)₁₁ = 4·U₂₂ ≠ 2) are airtight.
## Semantic audit
Literal conjecture (EN): "There exist two matrices with the same determinant and permanent but different integrality types, and the separation is realized by an explicit pair with the same values but different unimodular row transformations." (中文: 存在两矩阵的行列式与永久均相同而整型不同,分离由同值异幺模行变换的显式对实现。) This is an existential claim, so a single explicit pair legitimately proves it — there is no "whole family" to cover beyond the existential.

Final theorem (lean/Main.lean):
```
theorem conjecture_6330 : ∃ M N : Matrix,
    det M = det N ∧ permanent M = permanent N ∧
    SmithDiagonal M ∧ SmithDiagonal N ∧
    ¬ RowEquivalent M N ∧ ¬ RowEquivalent N M ∧ ¬ IntegerEquivalent M N
```
with witness ⟨B, A⟩, B = diag(2,2), A = diag(1,4).

Fidelity of definitions: `Matrix := Fin 2 → Fin 2 → Int`; `mul` is the correct 2×2 row-column product; `det M = M00*M11 − M01*M10`; `permanent M = M00*M11 + M01*M10` (sign-free, correct); `Unimodular U := det U = 1 ∨ det U = −1`; `RowEquivalent M N := ∃ U, Unimodular U ∧ mul U M = N` — exactly the conjecture's "unimodular row transformations"; `IntegerEquivalent` adds unimodular column operations (the coarser Smith-type equivalence, i.e. "integrality type"). `SmithDiagonal` (positive diagonal, divisibility) makes the distinct invariant factors (2,2) vs (1,4) explicit. The inequivalence lemmas quantify over ALL integer U, V with no entry bound or finite search: `no_row_transform_B_A` (parity: every entry of U·B = 2U is even, A has entry 1), `no_row_transform_A_B` ((U·A)₁₁ = 4·U₂₂ ≠ 2 over ℤ, closed by omega), `no_integer_double_transform` (evenness preserved under both-sided multiplication). These do not even use unimodularity, so they prove a strictly stronger separation than required.

Coverage of the statement: same determinant ✓ (both 4), same permanent ✓ (both 4), different integrality types ✓ (¬IntegerEquivalent plus ¬RowEquivalent in both orientations), explicit pair ✓, "same values but different unimodular row transformations" ✓. The theorem has zero hypotheses — nothing is strengthened; it is non-vacuous, constructively witnessed, and its numeric side is kernel-decided. This is exactly the historical rigor bar: the conjecture's objects (determinant, permanent, unimodular row transformations, Smith/integrality type) are all present and correctly defined, unlike the rejected PRs #286–288 pattern.
## Issues found
none blocking
## Verdict rationale
The Lean theorem is precisely the conjecture's existential statement with faithful definitions of determinant, permanent, unimodularity and row/two-sided equivalence, witnessed by diag(2,2) and diag(1,4) whose equal det/permanent (4,4) and distinct Smith types (2,2)/(1,4) I re-verified independently in Python. The project builds clean with only propext/Quot.sound as axioms, the PDF is genuine, all file hashes match, and no hypothesis is added or quietly strengthened — a complete, rigorous proof of Conjecture 00000006330 as literally stated.

## Disposition
APPROVED — merged into main (PR 356). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
