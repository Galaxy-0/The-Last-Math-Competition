# Solution Review — Conjecture 00000000205 (PR 379)

**Submission:** Galaxy-0 — `Galaxy-0_submission_20261004024529`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Conjecture and status:** `conjectures/00000000205.md` read in full. It asks that for every `n ≥ 2`, `Ulam(1,n)` be infinite, with the accompanying “density estimates” wording. Base `metadata.csv` marks the conjecture neither proven nor disproven, so this is not a duplicate accepted solution.
- **Scope:** `git diff --name-status 4cc82278...HEAD` adds only `solutions/00000000205/Galaxy-0_submission_20261004024529/`; no root, conjecture, metadata, leaderboard, or unrelated files are modified.
- **PDF/report:** I read the complete LaTeX report and all five pages of the shipped PDF. In a fresh copy, two independent `pdflatex` runs exited 0. Extracted text from the fresh and shipped PDFs is byte-identical; raw PDF differences are only compiler timestamp/banner metadata. No auxiliary computation is claimed or needed.
- **Lean build:** in a fresh copy, `lean --version` reported official Lean 4.31.0; `lake build` exited 0; direct `lean Ulam205Core.lean` also exited 0. The source SHA-256 is exactly the hash documented in the report.
- **Forbidden content:** targeted scan found no `sorry`, `admit`, `native_decide`, custom axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- **Axioms:** independent `#print axioms` output shows only `propext`, `Classical.choice`, and `Quot.sound` for the main existence/counting theorems, and only `propext` and `Quot.sound` for uniqueness. These are the permitted standard foundational axioms.

## What is proved

For every `n ≥ 2`, the report constructs the standard strictly increasing sequence beginning `1,n`, where each later term is the least integer above the current term with exactly one unordered representation as a sum of two distinct earlier terms. It proves existence at every stage, uniqueness of the sequence, infinitude, the growth estimate `a_(r+2) ≤ n·2^r`, and the counting lower bound `A_n(n·2^r) ≥ r+2`, hence `A_n(X) ≥ floor(log_2(X/n))+2` for `X ≥ n`.

The decisive extension argument is correct. In a finite increasing positive prefix with largest values `S < M`, `S+M` is an admissible distinct-pair sum. Another representation without `M` is at most `2S < S+M`; using `M` forces the other summand to be `S`. Therefore a candidate always exists, and well-ordering gives the least one. Recursion never assumes infinitude. The upper bound follows from `next < 2M`, and the counting bound follows from the first `r+2` distinct terms.

The report explicitly limits the quantitative claim to this logarithmic counting estimate and does not claim positive natural density or existence of a density limit. Since the bilingual conjecture specifies no density value, limit, or positive constant, this is an honest proof of its unambiguous infinitude claim together with a nontrivial quantitative counting estimate.

## Lean correspondence and semantic audit

`UniqueSum` represents unordered pairs of distinct values canonically as `a < b` and quantifies uniqueness over every `c < d` in the relevant membership predicate. `IsUlam` contains the two seeds, strict increase, exact earlier-pair uniqueness, and least choice; it is the standard rule, not a local-window or adjacent-pair variant. `stage_mem_iff` proves each recursive prefix contains exactly the preceding constructed values.

`sequence_isUlam`, `sequence_strictMono`, `sequence_unbounded`, and `sequence_infinite` establish the rule and infinitude. `exponential_upper_bound` and `counting_lower_bound` prove the same growth/counting conclusions for the same sequence. `sequence_unique` proves uniqueness. The added `range_below_is_earlier` and `sequence_global_uniqueSum` show that full-range representations of a selected non-seed term coincide with its earlier-prefix representations, closing the possible semantic gap. A temporary witness `S+M` is correctly used only to prove candidate existence, not assumed to be selected or permanently unique.

No conclusion is smuggled in as a hypothesis: `Prefix` carries only finite-prefix data, and the main theorem quantifies over every `n ≥ 2`. The formalization is non-vacuous and matches the report and official objects.

## Verification commands

```text
git checkout --detach pr/379
git diff --name-status 4cc82278...HEAD
shasum -a 256 -c SHA256SUMS
pdflatex -interaction=nonstopmode -halt-on-error report.tex   # twice
lean --version
lake build
lean Ulam205Core.lean
```

All exited successfully. Direct Lean axiom output was limited to the standard foundational axioms listed above.

## Verdict

**APPROVED.** The mathematical argument is correct, the report and formalization match the official statement as far as it is precisely specified, and all required builds and checks independently pass.
