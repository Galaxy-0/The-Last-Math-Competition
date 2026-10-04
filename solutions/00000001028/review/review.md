# Solution Review — Conjecture 00000001028 (PR 505)

**Submission:** jilint777 — `jilint777_submission_20261004151436`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Directly refutes the official “exactly 21 exceptions below 316” clause by exhibiting seven valid systems among the 26 admissible lower values.
- **Repository structure.** PR head `aada3eab...`, from clean base `4cc82278...`, adds only its correctly named folder. Base metadata has no prior solve.
- **LaTeX/PDF.** Read the full report and all six pages. Independently compiled twice; both passes exited 0. Ghostscript rendering succeeded.
- **Lean.** Independently built and replayed the self-contained Lean project; both commands exited 0. All audited theorems use only standard axioms.
- **Auxiliary code.** Ran `python3 verify.py`; exit 0 with all seven designs verified and `ALL CHECKS PASSED`.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or kernel-check bypass.

## Semantic audit

Only 26 values below 316 are congruent to 4 mod 12. Explicit, independently checked KQS designs for 4, 16, 28, 40, 52, 64, and 76 leave at most 19 possible exceptions (20 under a non-strict reading), so exactly 21 is impossible. Lean defines KQS literally and proves a sound checker for the explicit resolutions; Python independently validates the same designs and re-derives them from their constructions. Non-vacuity tests confirm small inadmissible orders fail.

## Issues found

None blocking.

## Verdict rationale

The counting disproof is elementary and decisive once the seven explicit systems are verified. Independent PDF, Python, Lean, axiom, structure, and semantic checks pass.

## Disposition

**APPROVED**
