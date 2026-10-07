# Solution Review — Conjecture 00000000407 (PR 646)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261005133946`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (bilingual): the statement counts nonzero entries of the LR coefficient table `(c^ν_{λμ})_{λ,μ,ν ⊢ n}` and claims the asymptotic `c·4^n/n^{5/4}`; the shipped `conjecture.md` is byte-identical to `conjectures/00000000407.md`.
- LaTeX: `report.tex` rebuilt independently with `latexmk -pdf` (exit 0, 5 pages, same as shipped). Extracted text of shipped vs. rebuilt PDF agrees; only engine-dependent hyphenation points and microtype spacing differ (cosmetic).
- Lean: `lake build` on the pinned Lean 4.19.0 / Mathlib project exits 0 with no errors and no warnings.
- Axioms: `#print axioms` for every decisive theorem (`LRTableau.size_balance`, `lrCoefficient_eq_zero`, `nonzeroCount_eq_zero`, `not_ratioAsymptotic`, `no_real_ratio_constant`, `conjecture407_false`, audit theorems) reports only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, or `extern` in the mathematical sources; the only grep hits are names of fields inside the verification tooling that audits for unsafe declarations.
- Auxiliary code: `python3 auxiliary/verify.py` runs in ~3 s, and its output is byte-identical to `auxiliary/expected-output.json`. It enumerates all 116,947 ordered triples for n ≤ 10 (nonzero counts 1, 0, …, 0) and cross-checks 4,170 coefficients against an independent Jacobi–Trudi Schur implementation, including Pieri cases and `c^{(3,2,1)}_{(2,1),(2,1)} = 2`.
- Integrity: all 153 files match `SHA256SUMS.json`.

## Semantic audit
The printed statement indexes the table by triples `(λ, μ, ν)` with **all three partitions of the same n**, in both the English and the Chinese text. The submission formalizes exactly this reading: `NonzeroEntry n` is the subtype of `Partition n × Partition n × Partition n` on which the coefficient is nonzero, and `nonzeroCount n` its cardinality — i.e., precisely the number of nonzero entries of the printed table.

The LR coefficient is defined by the conventional tableau model: semistandard fillings of the skew shape `ν/λ` (weak rows, strict columns), exact content `μ` for every letter (all trailing zero-content letters included as equations `0 = 0`), and the Yamanouchi/lattice prefix condition in the standard reading order (top rows first, right to left), which matches Mathlib's row-0-top Young diagram convention. Crucially, nothing about sizes is assumed: `LRTableau.size_balance` *derives* `|ν| = |λ| + |μ|` by counting skew cells against the content equations. Since `|λ| = |μ| = |ν| = n` would force `n = 2n`, every entry of the printed table vanishes for `n > 0` (`nonzeroCount_eq_zero`); the audit theorems confirm `A(0) = 1` (the empty tableau, unique by `empty_coefficient_one`) and `A(1) = A(2) = 0`.

The asymptotic claim is formalized as `RatioAsymptotic c := ∀ ε > 0, ∃ N, ∀ n ≥ N, |A(n)/(c·4^n/n^{5/4}) − 1| < ε` with the scale in `Real.rpow` (no integer-division exponent) and proved positive. `conjecture407_false : ¬∃ c, 0 < c ∧ RatioAsymptotic c` is the exact negation of the printed claim (a positive density constant is the only admissible reading of "density estimate ... c·4^n/n^{5/4}"); the stronger `no_real_ratio_constant : ¬∃ c : ℝ, RatioAsymptotic c` covers every real constant, so no reading of the constant's domain rescues the statement. The disproof does not strengthen any hypothesis of the official text — it exploits no quantifier asymmetry: the table it zeroes is the table the conjecture itself displays.

I independently verified the mathematics: `c^ν_{λμ} = 0` unless `|ν| = |λ| + |μ|` (homogeneity of Schur products / content counting) is a theorem of the standard definition, so the simultaneously-equal-size table is identically zero for every `n ≥ 1`; hence the ratio tends to 0 for any `c > 0` and no positive constant works. The report is explicit and honest that it does not address any "repaired" indexing (e.g., `|λ| + |μ| = |ν| = n`); under the ground-truth printed text this is the correct target, and attacking exactly the printed claim (rather than a strengthened reading) is precisely what the semantic audit requires.

## Issues found
- None blocking. The disproof is of the literal printed indexing; the report discloses this scope plainly, which is the right handling of an internally degenerate display convention in the source text.

## Verdict
APPROVED. Fresh LaTeX and Lean builds pass, axioms are exactly the standard three, the auxiliary exact computations reproduce byte-for-byte and corroborate the tableau definition, and the Lean negation matches the official bilingual statement quantifier-for-quantifier: the printed table is identically zero for `n > 0`, so no positive (indeed, no real) constant realizes `A(n) ~ c·4^n/n^{5/4}`.
