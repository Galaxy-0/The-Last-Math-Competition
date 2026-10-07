# Solution Review — Conjecture 00000004055 (PR 669)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005095613`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full from `conjectures/00000004055.md` (bilingual); shipped `conjecture.md` is byte-identical (`diff` clean). Extraction matches the PR tree file-for-file and hash-for-hash (15 files).
- LaTeX rebuilt independently with `latexmk -pdf` in a scratch dir; shipped vs rebuilt PDFs compared by normalized extracted text (pypdf) and rendered page images. Content identical; residual diffs are kerning/line-break extraction artifacts only.
- `lake build` in the submitted `lean/` project: success, 8708 jobs, zero errors, zero warnings. Toolchain Lean 4.33.1, Mathlib v4.33.1 rev 0df444a360 (prebuilt pool).
- Cheating scan clean: no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. Independent scratch `Check.lean` with `#print axioms` for all eight decisive theorems (`conjecture_4055_false`, `period_two_false`, `no_prime_period`, `period_eq_one`, `periodic_imp_period_one`, `minimal_period_is_one`, `selfInjective`, `simple_has_period_one`): only `propext`, `Classical.choice`, `Quot.sound`.
- Aux code: `verification/axioms.txt` and `verification/build.txt` reproduce exactly under my independent run. Minor blemish (non-blocking): `verification/SHA256SUMS.txt` is stale for `conjecture.md`; the shipped file is correct (byte-identical to the official) and all files match the PR git tree.
- Metadata: `metadata.csv` lists 00000004055 as `proven=false, disproven=false` at submission time; no competing solution on main.

## Semantic audit

The conjecture defines the syzygy Ω(M) as the kernel of the minimal projective cover and the period as the minimal number of iterations first returning to an isomorphic module, and claims that on every self-injective algebra any prescribed prime syzygy period p can be realized, with minimal period 2 attained by open-chain modules. The submission refutes this with the dual numbers A = k[ε], ε² = 0 (≅ k[x]/(x²)), a genuine self-injective algebra: self-injectivity is proven from Baer's criterion with the three ideal cases of k[ε] handled explicitly. The counterexample algebra satisfies the conjecture's own hypothesis, so this is a faithful disproof of the conjecture's own objects — no toy surrogate and no assumed theorem (the file builds everything from `import Mathlib`).

The mathematics is the standard structure theory of k[ε]-modules, formalized cleanly. (i) A superfluous submodule K of a projective A-module P lies in εP: if y ∈ K had a projective coordinate with nonzero constant term, the rank-one submodule L = {p : φ(p) ∈ εA} satisfies K + L = P (every p = c·y + (p − c·y)) while y ∉ L, contradicting superfluousness. (ii) Hence ε kills every syzygy (ε² = 0). (iii) If ε kills M, any projective cover π : P → M has ker π = εP, and p ↦ εp identifies P/ker π ≅ ker π, so ker π ≅ M. Consequently, if Ωⁿ(M) ≅ M for some n ≥ 1 then M is ε-killed, so already Ω(M) ≅ M: every periodic A-module has period 1, `no_prime_period` holds for every module and every prime (in particular 2), and the simple module εA (with A → εA a projective cover of kernel εA ≅ εA) witnesses that the minimal period over A is 1, not 2 — refuting both clauses of the conjecture, over a single self-injective algebra.

Two faithfulness points deserve note, both handled correctly. First, `IsSyzygy` is formalized as a relation (∃ a projective cover whose kernel is isomorphic to N) rather than via a chosen cover, so the non-realization result is robust: no module has prime period under any choice of covers, even ones chosen adversarially to favor periodicity. Second, the formalized clause `PrimePeriodsRealized` restricts the conjecture's universal quantifier to commutative finite-dimensional k-algebras; since k[ε] lies in that class and satisfies the conjecture's hypothesis (self-injective algebra) in the unrestricted sense, refuting the restricted clause refutes the original ∀-claim — the paper states exactly this. The scope section is honest: the stable-module-category reading and the undefined notion "open-chain module" are not formalized; note, however, that ε-killing of all syzygies and `period_eq_one` hold for plain module isomorphism, so they also defeat the stable reading informally. I verified the key computations over F₂[ε] independently (ker of multiplication by ε equals its range, equals εA, which is 1-dimensional with ε acting as 0, hence ≅ the simple module — period 1).

## Issues found

None blocking. (Verification-only: `verification/SHA256SUMS.txt` records a stale hash for `conjecture.md`; the file itself matches the official copy and the PR tree.)

## Verdict

APPROVED. A complete, faithful, and correct disproof: over the self-injective algebra k[x]/(x²) every syzygy is ε-killed and isomorphic to the module it comes from, so every periodic module has period 1 and no prime period — least of all period 2 — is realized. The Lean development proves self-injectivity from Baer's criterion, works with the conjecture's own definitions (projective cover, superfluous kernel, syzygy, period), is robust to the choice of covers and to modules of any cardinality, builds with zero errors and zero warnings, and passes the axiom and cheating audits with only the three standard axioms.
