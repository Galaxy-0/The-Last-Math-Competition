# Solution Review — Conjecture 00000007869 (PR 668)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005095248`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full from `conjectures/00000007869.md` (bilingual); shipped `conjecture.md` is byte-identical (`diff` clean). Extraction matches the PR tree file-for-file and hash-for-hash (15 files).
- LaTeX rebuilt independently with `latexmk -pdf` in a scratch dir; shipped vs rebuilt PDFs compared by normalized extracted text (pypdf) and rendered page images. Content identical; residual diffs are glyph-extraction artifacts only (one math symbol extracts differently between the two PDF builds).
- `lake build` in the submitted `lean/` project: success, 8708 jobs, zero errors, zero warnings. Toolchain Lean 4.33.1, Mathlib v4.33.1 rev 0df444a360 (prebuilt pool).
- Cheating scan clean: no `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. Independent scratch `Check.lean` with `#print axioms` for all six decisive theorems (`conjecture_7869_false`, `conjecture_7869_false_forall`, `conjecture_7869_false_eventually_frequently`, `conjecture_7869_false_limsup`, `conjecture_7869_false_tendsto`, `clauses_inconsistent`): only `propext`, `Classical.choice`, `Quot.sound`.
- Aux code: `verification/axioms.txt` and `verification/build.txt` reproduce exactly under my independent run. Minor blemish (non-blocking): `verification/SHA256SUMS.txt` is stale for `conjecture.md`; the shipped file is correct (byte-identical to the official) and all files match the PR git tree.
- Metadata: `metadata.csv` lists 00000007869 as `proven=false, disproven=false` at submission time; no competing solution on main.

## Semantic audit

The conjecture asserts three things about the random-order competitive ratio R_ro^n (expected competitive ratio under a uniformly random arrival order): (1) every deterministic online algorithm has R_ro^n ≥ 3/2 + ε₀ for an explicit positive ε₀; (2) Simple-Best-Fit achieves R_ro^n ≤ 3/2 + O(n^{-1/2}); (3) the optimal separation is the explicit jump from 4/3 to 3/2, determined by extremal bimodal instances. Clauses (1) and (2) are mutually inconsistent as stated: clause (1) quantifies over every deterministic online algorithm, and Best Fit is one, so (1) applied to Best Fit gives R_ro^n(BF) ≥ 3/2 + ε₀ with ε₀ > 0 independent of n, while (2) gives R_ro^n(BF) ≤ 3/2 + C/√n for all sufficiently large n, and C/√n → 0 — a contradiction for all large n. The submission proves exactly this, and the conjecture's falsity follows since its first two clauses cannot both hold.

The submission's strength is its grounding in the conjecture's own objects and its robustness under quantifier readings. Part 2 defines, concretely in Lean: n-item instances (sizes in (0,1]), deterministic online algorithms as decision functions of history, loads and current size, the execution semantics (`place`, `runAux`, `binsUsed`), Best Fit (fullest fitting bin, lowest index on ties), the offline optimum OPT, `expRatio` as the average of binsUsed/OPT over all n! permutations, and `Rro` as the supremum of expRatio over instances. For these concrete objects it proves `conjecture_7869_false : ¬(Clause1 ∧ Clause2)`, where Clause1 is the weakest standard reading (per-algorithm ε₀, "for infinitely many n") and Clause2 is the standard O-reading (eventually). Since ∀n ≥ 1 ⇒ eventually ⇒ infinitely often, the stronger readings are covered a fortiori, and the file additionally refutes each of them separately (`conjecture_7869_false_forall`, `_eventually_frequently`, `_limsup`, `_tendsto`), covering uniform-vs-per-algorithm ε₀ and the limit/limsup readings of clause 1. Part 1 abstracts the clash over an arbitrary ratio function and algorithm class — this is not a toy surrogate but a strengthening: the inconsistency does not depend on the precise definition of R_ro^n nor on the undefined name "Simple-Best-Fit", only that both clauses speak of the same ratio and that the named algorithm is deterministic and online (which clause 1 itself assumes of every algorithm). The paper's "not refuted" list is honest and correct: clause 1 read as "for some n", or both clauses read only as "for infinitely many n", escape the clash — those are not readings under which the conjecture is a coherent asymptotic statement anyway.

Faithfulness concerns from the review protocol do not apply: no deep theorem is assumed as a hypothesis (the clash lemmas take the two conjecture clauses as hypotheses, which is precisely the shape of ¬(A ∧ B)); the concrete bin-packing instantiation is the conjecture's own structure; the third clause is not formalized but needs no refutation, since it is conjoined with clauses that are already jointly contradictory (¬(A ∧ B) ⇒ ¬(A ∧ B ∧ C)). The only mathematical input is C/√n → 0, elementary and verified.

## Issues found

None blocking. (Verification-only: `verification/SHA256SUMS.txt` records a stale hash for `conjecture.md`; the file itself matches the official copy and the PR tree.)

## Verdict

APPROVED. The conjecture is self-contradictory — its first clause binds every deterministic online algorithm, including Best Fit, to a uniform random-order gap above 3/2 that its second clause denies Best Fit for large n — and the submission proves the exact negation over faithfully formalized bin-packing objects, robustly across every reasonable quantifier reading, with a clean build, standard axioms only, and an unusually careful account of what is and is not refuted.
