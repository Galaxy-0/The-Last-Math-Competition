# Solution Review — Conjecture 00000009939 (PR 752)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005204415`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (`conjectures/00000009939.md`, bilingual); shipped `conjecture.md` is **byte-identical** to it (`diff` empty).
- **LaTeX**: full `proof.tex` read; independent `latexmk -pdf -interaction=nonstopmode` rebuild succeeds (exit 0). Shipped vs rebuilt PDF text compared with pypdf after normalization: content matches; residual diffs are glyph-extraction artifacts only (big-operator/subscript font mappings between the author's MiKTeX fonts and the rebuild).
- **Lean build**: `lake build` completes with **zero errors and zero warnings** (8708 jobs). Toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360ea`, prebuilt pool.
- **Axioms**: independent `#print axioms` for `conjecture9939_false`, `bound_fails_every_count`, `no_constant_below_one`, `binary_reading_false`, `minEntropy_reading_false`, and `witness_211` each reports exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`, `admit`, `unsafe`, `extern`, `implemented_by`, or declared `axiom`.
- **Aux code**: `verification/axioms.txt` matches my independent run verbatim; `verification/build.txt` consistent with the fresh build; `SHA256SUMS.txt` mismatches fully explained as CRLF-vs-LF hashing artifacts (re-hash over CRLF reproduces the recorded value; shipped content identical).
- **Metadata**: `metadata.csv` lists 00000009939 as unproven and undisproven; no solution folder for it on `main`.

## Semantic audit

The conjecture defines persistence entropy as the Shannon functional of the persistence bar length distribution and asserts, as its explicit quantitative clause (both languages make this precise after the colon): E(B) − (longest-bar contribution) ≤ (1/2)·log(number of bars), with the constant claimed tight. The submission refutes exactly this clause — refuting the conjunction — via `conjecture9939_false : ¬ ConjecturedBound`, where `ConjecturedBound` is a verbatim transcription of the claim: for every nonempty barcode B, every longest bar I, `persistenceEntropy B - contribution B I ≤ (1/2) * log (barCount B)`. The definitions are the standard ones from the persistence-entropy literature (Atienza–Gonzalez-Diaz–Rucco 1701.07857; Atienza–Gonzalez-Diaz–Soriano-Trigueros 1803.08304, quoted in the report): a bar is a finite interval with positive length, a barcode a finite multiset of bars, E = Σ η(ℓᵢ/L) with η(x) = −x log x, and the contribution of I is its own summand η(ℓ_I/L) — the natural reading of the Chinese "熵减最长条贡献", and the two alternative readings of the English phrase are refuted as well (`binary_reading_false`, `minEntropy_reading_false`).

The counterexample family is `spike a m`: one bar [0,a) and m unit bars. For lengths (2,1,1) (`witness_211`): L = 4, E = (3/2) log 2, the longest bar contributes (1/2) log 2, so E − c = log 2 ≈ 0.6931 > (1/2) log 3 ≈ 0.5493 — a decisive violation with only n = 3 bars, all hypotheses satisfied (nonempty, positive lengths, unique longest bar). The general theorem `bound_fails_every_count` shows the bound fails for every bar count n ≥ 2: the gap is ((n−1)/(n+1))·log(n+1), and `key_ineq` proves (1/2)log(m+1) < (m/(m+2))log(m+2) for m ≥ 1 (case m = 1 via log 9 > log 8, i.e. 2^... 3² > 2³). Beyond refutation, `no_constant_below_one` shows no constant c < 1 works, so the true optimal constant is 1 and the conjecture's "tight constant" claim is false on its own terms; the witnesses have pairwise distinct bars and unique longest bars, so no multiplicity or choice-of-longest-bar loophole is exploited.

The mathematics is correct: I verified numerically that the gap exceeds (1/2)log n for all n from 2 to 7, that the m > 2/(1−c) witness works for c = 0.9, and both alternative-reading witnesses (S(16,48): (3/4)log 48 > (1/2)log 49 since 48³ > 49²; log 8 > log 7). Formalizing barcodes as abstract finite multisets is justified — Mathlib has no persistent homology — and the report supplies an explicit prose construction realizing any finite barcode as the degree-1 barcode of a wedge of hollow triangles with staggered filtration times, which is sound, and discloses its prose-only status. The vague "concentration inequalities" conjunct is not addressed, but refuting the quantitative conjunct refutes the conjunction. The one issue raised by the pre-submission semantic review (report statement of `no_constant_below_one` overclaiming uniqueness) was fixed in the shipped report, which now matches the Lean conclusion exactly.

## Issues found

None blocking.

## Verdict

APPROVED. The three-bar barcode (2,1,1) is a concrete, hypothesis-satisfying counterexample to the stated inequality, the failure is proved for every bar count ≥ 2 with no degenerate-witness tricks, the definitions match the standard persistence entropy and the conjecture's own clarified claim, and the development compiles cleanly using only the three permitted axioms. The conjecture is false.
