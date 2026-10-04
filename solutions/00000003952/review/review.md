# Solution Review — Conjecture 00000003952 (PR 504)

**Submission:** jilint777 — `jilint777_submission_20261004153915`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Refutes the official equivalence “twin-width ≤1 iff distance-hereditary” in both directions using the house and net graphs.
- **Repository structure.** PR head `38b54e88...`, from clean base `4cc82278...`, adds only its correctly named submission folder. Base metadata has no prior solve.
- **LaTeX/PDF.** Read the full report and all six pages. Independently compiled twice; both passes exited 0. Ghostscript rendering succeeded.
- **Lean.** Independently built and strictly replayed the self-contained Lean project; both commands exited 0. Final disproof theorems use only `propext` and `Quot.sound`.
- **Auxiliary code.** Ran `python3 verify.py`; exit 0 and `ALL CHECKS PASSED`, including exact partition-search twin-width, three DH tests, and graph enumeration through six vertices.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or kernel-check bypass.

## Semantic audit

The house has no twins, admits a width-1 contraction sequence, and is not DH because an induced path increases a distance from 2 to 3. The net is DH, but every initial contraction has red degree at least 2 and a width-2 sequence exists. Thus neither class contains the other, disproving the equivalence and hence the conjectured conjunction. Lean constructs trigraph contractions, widths, induced reachability, and DH from scratch; Python independently verifies all finite computations and small-graph classifications.

## Issues found

None blocking.

## Verdict rationale

The two explicit graphs decisively refute the stated equivalence. Independent PDF, Python, Lean, axiom, structure, and semantic checks pass.

## Disposition

**APPROVED**
