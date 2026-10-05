# Proof of conjecture 00000000106

For every natural `k >= 2`, the positive real exponent `c_k = 1/(2k)` works. The proof constructs a qualifying `n` beyond every prescribed bound, simultaneously for all shifts `n+1,...,n+k`, and proves the condition for their actual largest prime divisors.

Bertrand's postulate supplies distinct primes in successive dyadic intervals above a parameter `t`. A bounded Chinese remainder representative satisfies `t <= n < t^(2k)` and gives a prime divisor exceeding `t` for every shift. Thus every largest prime divisor exceeds `n^(1/(2k))`.

- `main.tex` and `main.pdf`: matching three-page proof and formalization report.
- `conjecture.md`: the exact bilingual source.
- `lean/`: pinned Lean 4.19.0 / Mathlib v4.19.0 project.
- `VERIFICATION.md`: reproduction commands and verification scope.
- `SEMANTIC_REVIEW.json`: separate nonauthor review of the frozen inputs.
- `verification/`: execution records, declaration and axiom audits, report checks, eligibility evidence and provenance.

The final theorem is `Conjecture106.conjecture : Conjecture106.Statement`. The greatest-prime-factor definition has a proved primality/divisibility/maximality specification on all inputs used in the theorem. The proof uses strict real powers and ordinary set infinitude. No external numerical computation is needed.

This submission was produced by AI. The author began with a fresh context containing only this candidate's source, guides and meaning assessment. The same agent performed that preliminary meaning assessment and authorship; the final nonauthor reviewer is separate. Local verification is distinct from maintainer acceptance.
