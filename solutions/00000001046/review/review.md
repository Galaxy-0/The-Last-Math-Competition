# Solution Review — Conjecture 00000001046 (PR 701)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005125726`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read; copy check.** Read `conjectures/00000001046.md` in full (bilingual). Shipped `conjecture.md` is byte-identical to it (`diff` clean).
- **LaTeX rebuild + PDF comparison.** `latexmk -pdf` on the shipped `proof.tex` in a scratch dir: exit 0, 3 pages matching the shipped PDF. Text extraction differs only in glyph-map/font-substitution artifacts around math (`3|q−1` extracting as `3jq1`, minus signs as `\x00`, single math letters merging with adjacent words); rendered pages are content-identical. Cosmetic.
- **Lean build.** `lake build` from scratch: zero errors, 8708 jobs, exit 0 (toolchain `leanprover/lean4:v4.33.1`, Mathlib v4.33.1, pool rev 0df444a360). Incremental rebuild of the extracted tree confirms the shipped sources match the built state.
- **Axioms.** No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere. Independent scratch check (`lake env lean Check.lean`) prints `[propext, Classical.choice, Quot.sound]` — only the standard three — for `four_le_diffUniformity`, `not_eventually_two`, `not_eventually_two_char_two`, `not_eventually_two_odd`, `four_le_diffCount`.
- **Aux code.** `Axioms.lean` reproduces `verification/axioms.txt`. Note: `verification/SHA256SUMS.txt` has two stale entries (`conjecture.md`, `lean/Conjecture1046/Basic.lean`) that do not match the shipped files; both were verified independently (copy identical to official; Lean built clean), so this does not affect any claim.
- **Metadata.** `metadata.csv` lists 00000001046 as unsolved (proven = false, disproven = false); no competing solution folder on main.

## Semantic audit

The conjecture states that the differential uniformity of x ↦ x + x^(q−2) over F_q is 2 for large q. The natural reading ("there is N such that δ(f_q) = 2 for every prime power q > N", likewise within q = 2^m or within odd q) is exactly what the submission refutes. Its decisive theorem `not_eventually_two` is ¬∃N, ∀ finite fields F with |F| > N, δ(f) = 2 — the exact negation — with two restricted variants (`not_eventually_two_char_two`, `not_eventually_two_odd`) covering the usual APN setting and the odd-characteristic setting.

The formalization is faithful to the conjecture's own objects. The map is defined as `x + x ^ (Fintype.card F - 2)` on an arbitrary finite field, and the differential uniformity as the maximum over a ≠ 0 and all b of the number of solutions of g(x+a) − g(x) = b, matching the standard (c = 1) definition quoted from the literature. Nothing is trivialized: the counterexample lives in real finite fields (`GaloisField 2 (2k)`, `GaloisField 7 k`), and the cube root of unity is obtained from Cauchy's theorem in F_q^×, not postulated.

The mathematics is correct, and I verified it independently. Whenever 3 | q−1, the equation f(x+1) − f(x) = 2 has the four distinct solutions 0, −1, ω, ω²: direct computation using ω² + ω + 1 = 0 gives f(ω+1) − f(ω) = (−ω² − ω) − (ω + ω²) = 2, likewise at ω², and the cases 0, −1 are immediate; distinctness holds in every characteristic (in char 2 the solutions are 0, 1, ω, ω²). Brute force over small fields confirms the pattern exactly: δ = 4 for prime fields q = 7, 13 (3 | q−1) and for GF(2^m) with m = 2, 4, and δ = 2 for q = 5, 11, 17 and m = 3 — so on the m-odd subfamily the conjecture's claim actually holds, which the README and proof.tex disclose honestly ("not refuted: a reading restricted to m odd, or to q = 3^k"). Since the conjecture as written quantifies over all large q (or all large q = 2^m, or odd q), the infinitely many counterexamples q = 4^k and q = 7^k refute it; refuting the explicit δ = 2 clause also falsifies the conjecture's parenthetical conjunction regardless of how the "uniqueness" remark is read.

The report also correctly diagnoses the defect of the earlier closed submission (three finite data points), and this submission fixes exactly that: the general statement is proved in Lean for every finite field, not sampled.

## Issues found

- Non-blocking: `verification/SHA256SUMS.txt` lists two hashes that do not match the shipped `conjecture.md` and `lean/Conjecture1046/Basic.lean` (stale checksums; both files verified correct independently). The other 12 entries check out.

## Verdict

APPROVED. The submission proves the exact negation of the conjecture's differential-uniformity clause, on the conjecture's own objects, with a general argument (δ ≥ 4 whenever 3 | q−1) that yields arbitrarily large counterexamples over all finite fields, over the characteristic-2 family, and over the odd-characteristic family; the Lean development builds with zero errors and depends only on the standard three axioms, and the mathematics was independently verified by hand and by exhaustive computation on small fields. The scope that survives (m odd) is explicitly and honestly out of scope of the refutation, which is the correct handling of an ambiguous "for large q".
