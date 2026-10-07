# Solution Review — Conjecture 00000000732 (PR 747)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005201755`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `/Users/xinranwang/Documents/GitHub/The-Last-Math-Competition-2/conjectures/00000000732.md` read in full (bilingual). Shipped `conjecture.md` is byte-identical to it (`diff` empty).
- LaTeX: rebuilt independently with `latexmk -pdf -interaction=nonstopmode`; succeeds. Shipped vs rebuilt PDF text compared with pypdf after normalization: content matches; only glyph-extraction artifacts (≥, ⇔, ligatures mapped differently by the authoring platform's fonts), cosmetic.
- Lean: `lake build` succeeds with zero errors and zero warnings (Lean v4.33.1, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474, prebuilt pool poolM04). Earlier "Too many open files" log entries were environmental (host fd limit), not a property of the submission.
- Axioms: `lake env lean Axioms.lean` prints `C732.conjecture732_false depends on axioms: [propext, Classical.choice, Quot.sound]`, matching `verification/axioms.txt`. Supplementary audit: `unitIndex_eq_one`, `witness_seven`, `asymptotic_fails` also only the standard three. No `sorry`/`native_decide`/`admit`/`unsafe`/`extern`/`implemented_by`/declared `axiom`.
- Aux code: `verification/` = `SHA256SUMS.txt`, `axioms.txt`, `build.txt`; every hash reproduces byte-exactly after LF→CRLF normalization; `axioms.txt`/`build.txt` match my independent rerun.
- Metadata: `metadata.csv` lists 00000000732 as unsolved; no solution folder on `main`.

## Semantic audit

The conjecture defines ε(m) as the index of the unit group of Q(ζ_m) over the norm-one units and claims (A) that the supremum of ε(m) grows like φ(m)/2^ω(m)·(1 + O(2^{−ω(m)})) as m → ∞, and (B) exact equality when m is an odd prime power. The submission formalizes the statement's own objects with Mathlib machinery: K = `CyclotomicField m ℚ` is genuinely the cyclotomic field, E = (𝓞 K)ˣ, `unitNorm` is the absolute norm N_{K/ℚ} restricted to E, `normOneUnits` is its kernel, and `unitIndex m` is the subgroup index; `claimed m = φ(m)/2^ω(m)` computed in ℚ (no rounding).

The disproof rests on a structural lemma proved in full Lean: in a totally complex number field the absolute norm is nonnegative, since N(x) = ∏_σ σ(x) groups over infinite places into pairs φ_w, conj∘φ_w whose product is |φ_w(x)|². A unit has |N(u)| = 1, hence N(u) = 1; so for m > 2 (where Q(ζ_m) is totally complex, via `IsCyclotomicExtension.Rat.isTotallyComplex`) the norm-one units are all units and ε(m) = 1 (`unitIndex_eq_one`). Meanwhile clause (B) demands ε(q) = φ(q)/2^ω(q) at odd prime powers; at the witness q = 7 this is 3, and `witness_seven` machine-checks ε(7) = 1 ≠ 3, so `conjecture732_false` refutes the conjunction. The refutation is robust well beyond the witness: ε(q) ≠ claimed(q) at every odd prime power q ≥ 7; any function bounded by 2 (hence any supremum of ε-values over any family, e.g. sup_{m' ≤ m} or sup_{m' ≥ m}) fails both asymptotic readings because φ(m)/2^ω(m) ≥ 5^k along products of k distinct primes ≥ 11 (`family`, `asymptotic_fails`); and the two most plausible alternative readings of "unit index" are also refuted — Hasse's index [E : W E⁺] ∈ {1, 2} (Mathlib `indexRealUnits_eq_one_or_two`) is never 3, and the relative-norm index [E : ker N_{K/K⁺}] is infinite (a fundamental unit η of K⁺ would force the non-torsion unit η to satisfy η^{2n} = 1), formalized as index = 0.

I verified the mathematics by hand: the norm-nonnegativity argument for totally complex fields is elementary and correctly transcribed; ε ≡ 1 for m > 2 follows immediately; φ(7)/2^{ω(7)} = 6/2 = 3. Quantifier structure is faithful — the formalized `Conjecture732` is exactly the conjunction of the asymptotic clause (for ε, with all suprema-families covered by additional conjuncts of the main theorem) and the exact-equality clause over all odd prime powers, and the disproof exhibits a concrete conductor satisfying all hypotheses (7 is an odd prime power) at which the claimed equality fails. No redefinition trivializes the claim: the literal definition is taken at face value and the alternative readings are dispatched as well.

## Issues found

None blocking. (SHA256SUMS mismatches are CRLF→LF normalization artifacts, reconciled byte-exactly; the unformalized small cases q = 3, 5 are correctly noted as unnecessary.)

## Verdict

APPROVED. A decisive, faithful disproof: under the conjecture's own definition, ε(m) = 1 for every m > 2 (all units of a totally complex field have absolute norm +1), while the conjecture demands ε(7) = 3; the exact-equality clause fails at m = 7 and every larger odd prime power, and the asymptotic clause fails under every reading of "supremum" and every plausible reading of "unit index". Build, axioms, report, and auxiliary verification files all check out.
