# Solution Review — Conjecture 00000001268 (PR 248)

**Submission:** orionsheep — `orionsheep_submission_20261003063544`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist
- [x] LaTeX source and PDF present
- [x] Lean 4 project compiles completely (lake build, exit 0)
- [x] No `sorry`, no `native_decide`, no extra axioms
- [x] Submission matches the conjecture's objects and literal statement

## Conjecture (verbatim summary)
The conjecture asserts that every infinite word can be repaired to a rich (rich-in-palindromes) word by at most one letter insertion, and that the minimal repair position is uniquely given by the defect center.

## What the submission proves
The Lean defines the 3-periodic lettering of (abc)^inf and proves the universal theorem no_pal: for every offset p and every length L >= 2, the factor is not a palindrome. Since one inserted letter leaves every position after it purely abc-periodic, any repaired word still contains a purely periodic length-5 factor whose only palindromic factors are eps, a, b, c — 4 distinct, below the 6 = 5+1 required by the classical Droubay-Justin-Pirillo richness criterion. Hence no single insertion repairs (abc)^inf, refuting the "every infinite word" claim.

## Verification notes
The palindrome argument re-derived independently (equal letters occur only at distances = 0 mod 3; a palindrome would force two consecutive such distances). reproduce.py enumerates all 9 single-letter insertions and confirms each leaves a non-rich length-5 factor. The richness criterion is classical, correctly applied, and flagged as cited in prose; the substantive core — absence of long palindromic factors, universally in offset and length — is fully kernel-certified. Note: an incomplete draft folder from the same PR was removed during merge; the audited folder is the complete submission.

## Verdict
APPROVED — merged into main.

