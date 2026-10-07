# Solution Review — Conjecture 00000000106 (PR 631)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261005103855`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (bilingual): "For every k ≥ 2 there exists c_k > 0 such that infinitely many n satisfy: the largest prime factor of each of n+1, …, n+k exceeds n^{c_k}". Shipped `conjecture.md` is byte-identical to `conjectures/00000000106.md`.
- LaTeX: `main.tex` rebuilt independently with `latexmk -pdf` (exit 0); 3 pages in both PDFs; extracted text identical after glyph/whitespace normalization.
- Lean: `lake build` exits 0 with no errors or warnings; `lake env lean Check.lean` exits 0.
- Axioms: all 6 `#print axioms` reports in `Check.lean` are exactly `[propext, Classical.choice, Quot.sound]`, including `unbounded_good` and the final `conjecture`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, or `extern` in the mathematical sources.
- Auxiliary code: none doing mathematics — the auxiliary programs (`Inspect.lean`, `Audit.lean`, `independent-verify.py`, `replay-author-inspection.py`) are provenance/inspection tooling; the report states "The mathematical argument requires no external numerical computation," which is accurate. I performed the numerical corroboration myself (below).
- Integrity: 57/57 files match `verification/SHA256SUMS.json`.

## Semantic audit
This is a **proof**, and the formal target is the source statement verbatim: `Statement := ∀ k ≥ 2, ∃ c > 0, {n | Good k c n}.Infinite` with `Good k c n := 2 ≤ n ∧ ∀ i ∈ [1, k], (n:ℝ)^c < P(n+i)`. The quantifier order (forall lengths k, then exists an exponent fixed for that k, then infinitely many n) matches the bilingual text exactly; "exceeds" is the strict inequality; `largestPrimeFactor` is proved (`largestPrimeFactor_spec`) to be the actual greatest prime divisor of m ≥ 2 with the characterizing equivalence `threshold_iff_prime_divisor`, so the inequality is about the true largest prime factor, and the "rough" word in the title introduces no extra condition (correctly so).

The proof is a clean elementary construction, exactly the one in the report. For fixed k ≥ 2 put c = 1/(2k) and given any N take t = max(2^k, N+k+3). Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`) supplies strictly increasing primes p_j ∈ (2^j t, 2^{j+1} t], hence pairwise coprime (`dyadic_primes`). CRT (`Nat.chineseRemainderOfFinset`) gives n ≡ −(j+1) (mod p_j) with the canonical representative bounded by the product; since 2^k ≤ t forces p_j ≤ t², one has t ≤ n < t^{2k} (`bounded_representative`; the lower bound t ≤ n comes from p_0 | n+1 and p_0 > t). Monotonicity of real powers gives n^{1/(2k)} < t < p_j ≤ P(n+j+1) for every j — simultaneously for all offsets — and since N < t ≤ n for every prescribed N, the qualifying set is unbounded and therefore infinite (`unbounded_good`, `Set.infinite_iff_exists_gt`). The theorem `conjecture` assembles exactly `Statement`. The proof establishes the claim with an explicit exponent (1/(2k)) — precisely what the existential clause asserts; nothing stronger is needed and nothing is smuggled in.

I verified the construction numerically with independent code: for k = 2, 3, 4, 5, 6 and N ∈ {10, 100, 5000}, the produced n satisfies the bounds and P(n+i) > n^{1/(2k)} for all i (e.g., k = 2, N = 100: t = 105, primes (107, 211), n = 2674, and both P(2675), P(2676) exceed 2674^{1/4} ≈ 7.2). The kernel-checked Lean development confirms this for all k and N.

## Issues found
- None. The proof is short, faithful, and complete; the "consecutive rough numbers" title in the source could suggest a stronger no-small-prime-factor reading, but the displayed condition concerns only the largest prime factor, and the submission correctly formalizes exactly the displayed condition.

## Verdict
APPROVED. Fresh LaTeX and Lean builds pass; axioms are exactly the standard three; the statement is formalized quantifier-for-quantifier; and the Bertrand + bounded-CRT construction — independently reproduced numerically — proves the conjecture for every k ≥ 2 with c_k = 1/(2k).
