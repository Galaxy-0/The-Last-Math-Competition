# Solution Review — Conjecture 00000006320 (PR 643)

**Submission:** Jackmeson1 — `solutions/00000006320/Jackmeson1_submission_20261005072301`
**Head:** `e0a8d62f3c99dd9768f6229980c8079b2cac2aa0`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06
**Result:** Approved

## Checklist results

- Official conjecture (`conjectures/00000006320.md`, English + Chinese) read in full; the submission's `conjecture.md` is byte-identical to it. Source-md check: pass.
- LaTeX report read in its entirety; independent `latexmk -pdf` rebuild succeeded; extracted text of shipped and rebuilt PDFs matches modulo standard glyph/ligature extraction artifacts (`per`, `supp` operator-font spacing, `ff`/`fi` ligatures). PDF-match check: pass.
- `lake build` (Lean v4.33.1, Mathlib v4.33.1) exits 0 with zero errors and zero warnings. Lean-build check: pass.
- No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. `#print axioms Conjecture6320.separation` → `[propext, Classical.choice, Quot.sound]` only, independently re-run via the shipped `Axioms.lean`. Axiom check: pass.
- Auxiliary `verification/` material (`build.txt`, `axioms.txt`) agrees with independently reproduced results; two SHA256SUMS entries (`conjecture.md`, `lean/Conjecture6320/Basic.lean`) hash CRLF newline variants of the shipped files — a bookkeeping artifact, content identical. Aux check: pass.
- Semantic audit: pass (details below).

## Semantic audit

The conjecture asks for two matrix classes with the same permanent lower-bound constant but different support structures, the separation realized by an explicit pair with the same constant but different support families. The Lean decisive theorem `separation` matches this quantifier-for-quantifier: `Omega2` (Mathlib's `doublyStochastic ℝ (Fin 2)`) and `Omega2pos` (its all-entries-positive subclass) satisfy `IsLeast (permanent '' Omega2) (1/2)`, `IsLeast (permanent '' Omega2pos) (1/2)`, hence equal infima `lbConst Omega2 = lbConst Omega2pos = 1/2`, while `suppFamily Omega2 ≠ suppFamily Omega2pos`; the identity matrix witnesses a support (the diagonal) in the first family and absent from the second (`supp 1 ∉ suppFamily Omega2pos`). The constant is proved in the strongest useful sense — an attained least element, not merely an infimum — so "lower-bound constant" is faithful to the optimal-bound reading suggested by the conjecture's reference to the permanent lower bound (the van der Waerden context), and `const_eq_vdW` confirms 1/2 = 2!/2².

I rederived the mathematics. Every 2×2 doubly stochastic matrix has the form `[[a, 1-a], [1-a, a]]` with `0 ≤ a ≤ 1` (`Omega2_form`, `Omega2_bounds`), so `per M = a² + (1−a)² = 1/2 + 2(a−1/2)² ≥ 1/2`, with equality iff `a = 1/2` (`perm_eq`, `perm_ge_half`, `perm_eq_half_iff`). `J₂/2` (all entries 1/2) is positive doubly stochastic with permanent exactly 1/2, so the constant 1/2 is attained in both classes. The support analysis is exact, not just a difference: `suppFamily Omega2⁺ = {univ}` (every positive matrix has full support; `J₂/2` realizes it) and `suppFamily Omega2 = {diagonal, anti-diagonal, univ}` (a = 1 gives the identity/diagonal, a = 0 gives the swap/anti-diagonal, 0 < a < 1 gives full). In particular the families genuinely differ, even up to support cardinality (2 nonzero entries occur in Ω₂, never in Ω₂⁺), as the report's remark notes.

Faithfulness of definitions: "support" is the set of nonzero positions (`supp`), "support family" the set of supports of members (`suppFamily = supp '' C`) — the natural reading of "support structure/family" in the bilingual text; the permanent is Mathlib's `Matrix.permanent`, computed for Fin 2 as `M 0 0 M 1 1 + M 1 0 M 0 1` (`permanent_fin_two`). The conjecture is existential and is established by one explicit pair; nothing is strengthened or weakened. The two classes are distinct sets (Ω₂⁺ ⊊ Ω₂, witnessed by I₂), so the "two matrix classes" clause is nondegenerate.

Build hygiene: zero errors/warnings; axiom profile is the allowed minimum, replayed independently. The report matches the code (all theorem names it lists exist and state what it claims).

## Issues found

- Minor: two entries of `verification/SHA256SUMS.txt` hash CRLF newline variants of `conjecture.md` and `lean/Conjecture6320/Basic.lean` (verified by re-hashing after newline normalization). Non-blocking hygiene issue.

## Verdict

APPROVED. A correct, fully machine-checked constructive proof of the existential conjecture with an exact computation of both support families, a clean build and axiom profile, and a report that faithfully mirrors the Lean development.
