# Solution Review — Conjecture 00000003891 (PR 773)

**Submission:** Jackmeson1 — `solutions/00000003891/Jackmeson1_submission_20261005222022`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (English + Chinese, `conjectures/00000003891.md`); shipped `conjecture.md` is **byte-identical** to it (`diff` empty).
- **LaTeX:** entire `proof.tex` (162 lines) read; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch dir (build succeeds). pypdf text comparison of shipped vs rebuilt PDF: identical alphanumeric content; the only differences are glyph-extraction artifacts of the different TeX font subsetting (subscript `p`/`x` of `x_i^{p^i}` dropped or extracted by pypdf; no letters, words or claims differ).
- **Lean build:** `lake build` succeeds with zero errors and zero warnings on this machine — Lean **v4.33.1**, Mathlib **v4.33.1** (pool rev `0df444a360`), toolchain from the shipped `lean-toolchain`. Log: `pr773/lake-build.log` ("Build completed successfully (8708 jobs)"), matching the shipped `verification/build.txt`.
- **Axioms:** no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere in the project. Independent `lake env lean Check.lean` with `#print axioms` for `C3891.main_theorem` and `C3891.haar_ne_zero`: only `[propext, Classical.choice, Quot.sound]` — matches the shipped `verification/axioms.txt` exactly.
- **Aux code:** no aux scripts shipped; `verification/` outputs were re-derived (build log, axiom printout). `SHA256SUMS.txt` mismatches on `conjecture.md`, `Basic.lean`, `proof.tex` are commit-time CRLF→LF normalization: the shipped sums equal the SHA-256 of the CRLF variants (verified byte-wise for `proof.tex`); binary files pass. Cosmetic only.
- **Metadata:** `metadata.csv` lists 00000003891 as unsolved; the PR adds only its own submission folder.

## Semantic audit

The conjecture is a conjunction: (I) "the recursion recovering Witt components from a ghost sequence always has a unique solution", and (II) "ghost sequences making component p-adic valuations unbounded form a measure-zero closed set in the compact topology". The submission works with Mathlib's genuine p-typical `WittVector p R` and `WittVector.ghostComponent n x = Σ_{i≤n} p^i x_i^{p^{n-i}}` (proved equal to the Witt polynomial in `ghost_formula`), with ghost sequences in the compact product space `(ℕ → ℤ_[p])` — the natural reading of "the compact topology". Nothing is toy or surrogate: the decisive objects are the conjecture's own.

The refutation covers every non-degenerate reading of the ambiguous text. Reading A (integral components): the ghost sequence `e1 = (0,1,0,…)` has no preimage in `W(ℤ_[p])`, since `w_0 = x_0 = 0` forces `p·x_1 = 1` with `‖p·x_1‖ ≤ p^{-1} < 1` (`e1_not_ghost`), so clause (I) fails over ℤ_p; this alone falsifies the conjunction. Reading B (components recovered in ℚ_[p], where `ghostEquiv` makes clause (I) true): a strong-induction ultrametric dominance argument (`norm_comps`, `comps_ne_zero_val`) shows that on the nonempty open set `U = {w : ‖w 1 - w 0 ^ p‖ = 1}` the recovered components satisfy `v(x_n) = -(1+p+…+p^{n-1})` for all n ≥ 1, so the unbounded-valuation set contains `U` and has positive measure for every measure positive on nonempty open sets, in particular every additive Haar measure (`measure_ne_zero`, `haar_ne_zero`); clause (II)'s "measure-zero" fails for the unbounded-below and absolute-unbounded readings. Reading C ("unbounded above"): the explicit integral Witt vectors `x^{(k)} = (1,…,1,p^k,p^{k+1},…)` have ghost sequences converging to `ghost(1,1,1,…)` (coordinatewise, hence product topology), all inside `UnbddAbove`, while the limit has all component valuations 0 and is outside even the most permissive variant `UnbddAboveTop`; hence no intermediate set is closed in `(ℕ → ℤ_[p])` nor relatively closed in the ghost image of `𝕎 ℤ_[p]` (`not_closed`, `not_closed_in`). Finally the literal printed formula `w_n = Σ x_i^{p^i}` (unweighted, despite the text calling them "weighted power sums") is refuted at `(0,p,0,…)` (`lit_no_solution`: `x_1^p = p` is impossible in ℚ_p since `p ∤ 1`).

The mathematics is correct: I re-derived the n=1 and induction steps of `norm_comps` (the i = n+1 term `p^{n+1}x_{n+1}^p` strictly dominates all smaller terms and `w_{n+2}` by the `key` exponent inequality and the ultrametric inequality), and verified numerically for p = 2 with w = e1 that the recovered components are `1/2, -1/8, -3/128, -27/32768, …` with `v(x_n) = -(2^n - 1)` exactly, as claimed. The faithfulness gate is satisfied: no hypothesis assumes the negated statement, and no toy instance is substituted. The report honestly discloses the readings not covered (non-compact ℚ_p^ℕ; the degenerate integral-ghost-image + unbounded-below reading, where the set is empty) — these cannot rescue the conjecture as written, because clause (I) is asserted for every ghost sequence and the conjunction fails under each standard reading.

## Issues found

None blocking. (Cosmetic: `verification/SHA256SUMS.txt` was computed on CRLF working-tree files, so three text files mismatch after git's CRLF→LF normalization; the shipped sums match the CRLF variants exactly, so content integrity is unaffected.)

## Verdict

APPROVED. The submission is a faithful, complete, machine-checked disproof of the conjecture as stated: for every prime p it refutes clause (I) in the integral reading, refutes clause (II)'s measure-zero claim for unbounded-below/absolute readings and its closedness claim for the unbounded-above reading (in the ambient compact space and in the ghost image), and refutes clause (I) for the literal printed formula. The Lean build is clean, the axiom footprint is exactly the standard three, and the report matches the formalization.
