# Solution Review — Conjecture 00000005402 (PR 723)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005154816`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000005402.md` read in full (bilingual). Shipped `conjecture.md` diffed against it: byte-identical.
- LaTeX: entire `proof.tex` read (193 lines). Independently rebuilt with `latexmk -pdf -interaction=nonstopmode` in a scratch directory; build clean. Shipped vs rebuilt PDF text compared with pypdf: content matches; only ligature (`ff`/`fi`) and math-glyph extraction artifacts (`\mu(d)d` fragments, hyphenation) differ — cosmetic.
- Lean build: `lake build` succeeds with **zero errors and zero warnings** (8708 jobs; Lean toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360ea` from the prebuilt pool, linked via `.lake/packages`).
- Cheating greps: no `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere in `lean/`.
- Axioms: `Axioms.lean` re-run independently via `lake env lean Axioms.lean` plus a scratch `Check.lean` covering `g_counterexample`, `R1_no_integer_conversion`, `no_placement_of_muD` — every decisive theorem reports exactly `[propext, Classical.choice, Quot.sound]`. Matches shipped `verification/axioms.txt`.
- Aux code: no scripts shipped; `verification/` files checked. `axioms.txt` reproduced exactly; `build.txt` consistent with an independent successful build; three entries of `SHA256SUMS.txt` (`conjecture.md`, `Basic.lean`, `proof.tex`) fail `sha256 -c` **only** because the author hashed the CRLF working-tree copies — re-hashing with CRLF endings reproduces the recorded sums exactly, and the committed (LF) `conjecture.md` is byte-identical to the official file. Benign, noted.
- Eligibility: `metadata.csv` lists 00000005402 unsolved; no `solutions/00000005402/` on `main`; the PR adds only the 15 files of this submission folder.

## Semantic audit

The conjecture asserts a conjunction about the Mobius conversion from counts of all periodic orbits to primitive (exactly periodic) orbit counts: (i) at low order it is an explicit divisor-sum recursion with coefficients of type mu(d)*d, (ii) its transfer matrix is triangular with unit diagonal, (iii) the inverse cumulative conversion is a partial sum with nonnegative coefficients. The submission attacks clause (i) at order 2 — the lowest order at which the clause says anything beyond B_1 = T_1 — which falsifies the conjunction; clauses (ii) and (iii) are neither needed nor claimed false.

Because the text does not pin down whether points or orbits are counted, the submission enumerates six readings of (total T, primitive B): (perPts, primOrbits), (perPts, exactPts), (divOrbits, primOrbits) and their cumulative variants, and refutes all six at once with a single witness, the permutation g = (0)(1)(2 3) of Fin 4 (Lean `g`, all values by `decide` after reduction of involutions to Mathlib's `minimalPeriod`/`periodicOrbit`). The counts are perPts g 1 = 2, perPts g 2 = 4, exactPts g 2 = 2, primOrbits g 2 = 1, divOrbits g 1 = 2, divOrbits g 2 = 3 (I re-verified all six numerically), so the conjectured conversion sum_{d|2} mu(d) d T(2/d) = T_2 - 2 T_1 predicts 0 (R1, R2) and -1 (R3) against true values 1, 2, 1. The decisive theorem `conjecture_5402_false` is the negation of `ConjecturedConversion` under all six readings, quantified exactly as the conjecture's universal statement ("always", i.e. over every finite dynamical system and every 1 <= n <= N, for every N >= 2).

The formalization is faithful: it uses Mathlib's own `ArithmeticFunction.moebius` and `Nat.divisors` for the mu(d)*d coefficients, and Mathlib's `periodicOrbit`/`minimalPeriod` for the orbit counts — the conjecture's own objects, no redefinitions that trivialize the claim, no hypotheses assumed. Two further theorems remove the residual ambiguity escape route: under R1 no order-2 conversion with integer coefficients exists at all (Unit identity gives 0 = x + y, the Bool swap gives 1 = 2x), and under R2/R3 any such conversion is forced to have coefficients (1, -1) = (mu(1), mu(2)) — so -2 = mu(2)*2 fits in neither slot (`no_placement_of_muD`). My own computation confirms these forced pairs and that the true classical order-2 coefficients are mu(d), not mu(d)*d, under both standard point- and orbit-count readings. The paper's Scope section honestly discloses the one reading not treated (a repetition-weighted total T_n = sum (n/k) B_k, which the conjecture text does not mention and under which mu(d)*d would be correct); this does not affect the refutation of the statement as written.

The mathematics is correct: I brute-forced the witness and the coefficient-forcing systems independently and they match the paper and the Lean statements exactly. The LaTeX report's numbers, theorem statements and axiom-audit claims agree with the Lean source line by line.

## Issues found

None blocking. (Minor, noted: three `SHA256SUMS.txt` entries mismatch the committed LF files because the author hashed CRLF working-tree copies; content is identical modulo line endings.)

## Verdict

APPROVED. This is a faithful, complete, and honest disproof of the first clause of Conjecture 00000005402 at order 2, with a genuine dynamical-system witness, coverage of every natural reading of the ambiguous counting conventions, a supplementary uniqueness theorem showing no placement of the coefficients mu(1)*1 = 1 and mu(2)*2 = -2 can satisfy the conversion under any reading, zero-error Lean build, and only the three standard axioms.
