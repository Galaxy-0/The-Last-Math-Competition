# Solution Review — Conjecture 00000002139 (PR 785)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261006003852`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** PROOF. **Conjecture:** floor-sum Euclidean recursion.

## Checklist results

- **Official conjecture.** `conjectures/00000002139.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The official text says of the floor-sum's recursion only that 'the complexity of its recursion is logarithmic' and 'the recursion path is the Euclidean algorithm'. The submission selects the standard Euclid-like recursion (reduce a, b mod m; add the quotient contribution; swap modulus and slope — the ACL/OI-wiki algorithm) and formalizes both natural stopping rules. The object itself is faithful: `floorSum n m a b = ∑_{i<n} (a*i+b)/m` on ℕ, proved equal (`floorSum_cast`) to the genuine rational-floor sum; `euclidTrace` records exactly the argument pairs of the remainder recursion of `Nat.gcd`.

The decisive theorem `C2139.floorSum_recursion_euclid` states, for all n, a, b and m ≥ 1, the conjunction: `floorSum = floorSumInt`; `fsRec` computes `floorSum`; its path *equals* `euclidTrace m a`; the last modulus on the path is `Nat.gcd m a`; the path length is at most 2·log₂ m + 1 and at most 2·log₂ min(a, m) + 2; and `aclRec` (the AtCoder early-exit loop) computes `floorSum` with path a *prefix* of the same Euclid trace and the same upper bound. The path equality is the conjecture's 'recursion path is the Euclidean algorithm'; the bounds plus the Fibonacci lower bound `fsRec_fib` (exactly k+1 calls on (F_{k+2}, F_{k+3}), with F_{k+2} ≤ 2^k) make the worst-case complexity Θ(log m) — the conjecture's 'complexity is logarithmic', proved as a tight two-sided statement. For `aclRec` the scoping is exactly right: full trace equality would be false for an early-exit loop, and the submission (after its own pre-submission semantic review, documented in SEMANTIC_REVIEW.md) claims only correctness + prefix + upper bound.

I checked the mathematical heart independently: the reduction identity for each summand, the rows/columns lattice-point swap `F(n,m,a,b) = F(⌊y/m⌋, a, m, y mod m)` (proved in Lean by double counting with `sum_range_reflect`), the 2s < x step in the Lamé bound, and numerically that Euclid on (F₉, F₁₀) = (34, 55) takes 8 = k+1 steps while 2·log₂ 34 + 1 = 12. Signed a, b are reduced by one honest normalization step (`floorSumInt_normalize`). No hypothesis is strengthened beyond m ≥ 1 (the m = 0 convention is quarantined), and everything proved is stronger than the conjecture requires.

## Issues found

None material. The build log is clean (no warnings). The pre-submission SEMANTIC_REVIEW.md documents one presentation issue (an over-broad claim about `aclRec`), which was fixed in the final text and code.

## Verdict

APPROVED. The submission proves exactly the two claims of the conjecture — logarithmic recursion complexity (with matching upper and lower bounds) and the recursion path coinciding with the Euclidean algorithm — with faithful definitions, exact trace equality, a clean build, clean axioms, and honest scoping of the early-exit variant.
