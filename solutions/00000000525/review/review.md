# Solution Review — Conjecture 00000000525 (PR 713)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261005203313`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read in both languages; `original_conjecture.md` is byte-identical to the official `conjectures/00000000525.md`.
- Change policy: only the declared submission folder is added; no metadata, conjecture, root, or unrelated files are changed.
- LaTeX: independently rebuilt with `latexmk -xelatex` (ctex document, exit 0). Shipped and rebuilt PDFs contain identical text.
- Lean: fresh `lake build` under Lean 4.19.0 / Mathlib `c44e0c8e...` succeeded with zero errors and zero warnings.
- Axioms: independent `#print axioms` on `local_conjecture_false`, `global_conjecture_false`, `fpt_ne_five_sixths`, `globalFpt_ne_five_sixths`, and `admissible_bound` shows only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe definition, `implemented_by`, or `extern`.
- Auxiliary code: the bespoke independent verifier (fresh copy, strict warnings-as-errors replays, 63-declaration audit, nine dependency pins) exited 0 under my run. The report correctly states there is no numerical computation supporting the mathematics.
- Duplicate status: base metadata marks 00000000525 unproven and undisproven.

## Semantic audit
The conjecture is a conjunction: the limit of fpt(x²+y³) as p → ∞ equals the characteristic-zero log threshold, and for p ≡ 2 (mod 3), fpt = 5/6. The submission refutes the second conjunct at p = 5, which is prime and satisfies 5 mod 3 = 2 (machine-checked); since the exact-value assertion is stated without any "eventually" qualifier in either language, one small prime refutes it, and the refutation holds for every real candidate limit value L, so the conjunction falls for all readings of the first conjunct.

The formal definitions are faithful. The F-pure threshold is the standard all-level supremum sup{n/p^e : f^n ∉ (x^{p^e}, y^{p^e})}, with genuine Frobenius powers of the origin maximal ideal over `MvPolynomial (Fin 2) K`; the e = 0 level is proved harmless (`allLevels_eq_positive`); real suprema are taken over provably nonempty, bounded sets, with no default values. The global reading is covered as well: the infimum of the F-thresholds c^I(f) over all maximal ideals containing f is formalized, the origin is proved maximal (kernel of the surjective evaluation), and the chain globalFpt ≤ c^origin ≤ fpt_0 ≤ 4/5 is proved, so the disproof is robust under both the origin-local and global interpretations of "the" F-pure threshold.

The algebra is correct and I verified it independently. Over ℤ, (x²+y³)⁴ = x⁵(x³+4xy³) + y⁵(6x⁴y+4x²y⁴+y⁷), which the Lean kernel checks by ring normalization; in characteristic 5 the freshman's-dream lemma `frobenius_mem` propagates f⁴ ∈ (x⁵, y⁵) to f^{4·5^e} ∈ (x^{5^{e+1}}, y^{5^{e+1}}) at every level, so any admissible exponent satisfies n < 4·5^e and n/5^{e+1} ≤ 4/5. The bound is in fact attained (at level 25, n = 20), so the true fpt over F_5 is exactly 4/5 — comfortably below the claimed 5/6. This is consistent with the known interpolation (5p−1)/(6p) at p = 5 and confirms that the printed residue class formula (which in reality holds for p ≡ 1 mod 3) is simply false as written; the submission rightly disproves the printed text rather than a corrected version.

## Issues found
None blocking.

## Verdict
APPROVED. The characteristic-5 Frobenius bound is correctly stated, correctly proved, and correctly quantified under both readings of the threshold; it refutes the printed p ≡ 2 (mod 3) clause at p = 5 and hence the conjecture's conjunction, and all independent builds, axiom audits, and verification tooling pass.
