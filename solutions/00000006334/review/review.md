# Solution Review — Conjecture 00000006334 (PR 311)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — Weighing matrices W(n,k) (entries 0/±1, WW^T = kI); conjecture asserts existence is characterized by a "square decomposition" of the weight whose sum is the matrix order, the order is EVEN, and the existence-window lower bound is k+2 attained by conference types.
- LaTeX: compiled ok (pdflatex twice, exit 0), 2-page PDF; included main.pdf is a genuine PDF, page count matches verification.json (2 pages).
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (warnings-as-errors), toolchain v4.19.0, imports only Std.
- Forbidden content: none — grep found no sorry/admit/native_decide/axiom/unsafe/implemented_by/extern.
- Auxiliary code: no scripts present (`auxiliary_scripts_rerun: []`). I ran an INDEPENDENT Python check: circulant W(7,4) has entries in {0,±1}, W W^T = 4 I_7 (all 49 pairs), matches the tex-displayed matrix exactly; C4 gives C C^T = 3 I_4, zero diagonal, off-diag ±1, 4 < 3+2. sha256 of Main.lean/main.tex match verification.json; reproduced axiom printout (propext only, some theorems axiom-free) matches lean-verification.txt.
## Semantic audit
Conjecture's literal clause (EN: "the sum of the decomposition is the matrix order, even"; CN: "分解的和为矩阵阶且阶为偶") explicitly asserts the matrix order is even.

Lean definitions verified faithful:
- `Matrix n := Fin n → Fin n → Int` (exactly n rows/cols); `IsWeighingMatrix k W := (∀ i j, W i j ∈ {0,1,-1}) ∧ (∀ i j, rowInnerProduct W i j = if i = j then k else 0)` — exactly the standard W(n,k) definition (WW^T = kI_n), computed over `List.finRange n` (all columns).
- `W7` is the circulant with first row (1,-1,-1,0,-1,0,0); `W7_displayed_rows` proves equality with the exact matrix displayed in main.tex (LaTeX↔Lean correspondence is machine-checked, not just claimed); `W7_entries` and `W7_orthogonality` check all 49 entries and all 49 row-pair inner products by kernel `decide`.
- Hypotheses: `W7_is_weighing : IsWeighingMatrix 4 W7` — the counterexample IS a weighing matrix. `odd_order_counterexample : ∃ n k W, 0 < k ∧ k < n ∧ k + 2 ≤ n ∧ IsWeighingMatrix k W ∧ n % 2 = 1` — the witness has positive nonfull weight AND satisfies the conjectured window bound n ≥ k+2 (7 ≥ 6), so it survives even the most favorable reading of the ambiguous "window" restriction.
- Final theorems: `ClaimedEvenOrder := ∀ (n k) (W : Matrix n), IsWeighingMatrix k W → n % 2 = 0`; `claimed_even_order_false : ¬ ClaimedEvenOrder`; `even_order_claim_fails_under_bound` (still false with 0<k<n and k+2≤n hypotheses); `full_conjecture_false (OtherAssertions) : ¬ (ClaimedEvenOrder ∧ OtherAssertions)`.
- Logical contradiction: conjecture says every (window-eligible) weighing matrix has even order; W(7,4) exists (kernel-verified) with order 7 odd. Genuine contradiction, not vacuous — the decisive object (an actual weighing matrix) is present and fully verified.
- Supplementary: conference matrix W(4,3) (C C^T = 3I_4, zero diagonal, ±1 off-diagonal, `C4_is_conference`) refutes the n ≥ k+2 bound reading, in the very "conference" subclass the conjecture names. Independent of the main result.
- Conjecture is admittedly machine-translated and partly vague ("conversion constant", "window", "square decomposition"), but the even-order clause is unambiguous in both languages, and the counterexample additionally satisfies the k+2 bound and 0<k<n, so no plausible restriction rescues the conjecture.
## Issues found
- None blocking. Note (non-blocking): conjecture's remaining clauses are too vague to formalize; submission correctly targets the precise even-order clause, with the bound clause addressed supplementarily.
## Verdict rationale
W(7,4) is a genuine, kernel-verified weighing matrix of odd order with positive nonfull weight satisfying n ≥ k+2, directly contradicting the conjecture's explicit even-order assertion under every plausible reading. Everything compiles warning-free, the LaTeX matches the Lean bit-for-bit (checked by `W7_displayed_rows` and my independent Python), and no forbidden content exists.

## Disposition
APPROVED — merged into main (PR 311). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
