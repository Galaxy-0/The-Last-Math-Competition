# Solution Review — Conjecture 00000000126 (PR 329)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003104000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — for every a ≥ 2 there are infinitely many primes of the form 1 + a + a² + … + a^k (k+1 prime a necessary condition).
- LaTeX: compiled ok (pdflatex twice, exit 0, 0 errors); included main.pdf real PDF v1.5, 2 pages, matches tex; verification.json pages=2.
- Lean build: fresh build after `rm -rf .lake`, exit 0, no warnings (`-DwarningAsError=true`); axioms match lean-verification.txt (propext, Quot.sound only).
- Forbidden content: none (grep over sorry/admit/native_decide/axiom/unsafe/implemented_by/extern returned nothing).
- Auxiliary code: no scripts shipped (`auxiliary_scripts_rerun: []`); `independent-check.json` is a data record — I re-verified all 12 rows with my own python3: repunit values n=0..11 match; factorization formula verified for n=3..59,97,101,103; trial division over n<30 finds the only prime at n=2 (value 5); Fermat witnesses confirm n=31,37 composite.
## Semantic audit
Conjecture literal claim: "for every a ≥ 2 there are infinitely many primes of the form 1 + a + … + a^k". Refuted at a = 4, which satisfies the hypothesis a ≥ 2.

Lean definitions faithful: `repunit a n` recurses to 1 + a + … + a^{n-1} (length n = k+1 in the source, as SOURCE.md documents); `IsPrime p := 2 ≤ p ∧ ∀ a b, p = a*b → a = 1 ∨ b = 1` is the ordinary primality definition. The key content is symbolic over all lengths, not a bounded search:
- `geometric_identity (n) : 3 * repunit 4 n + 1 = 4 ^ n` (induction), hence `square_identity : 3 * repunit 4 n + 1 = 2^n * 2^n`.
- `pow_two_nonzero_mod_three (n) : 2^n % 3 = 1 ∨ 2^n % 3 = 2` (induction).
- `all_long_repunit_composite (n) (hn : 3 ≤ n) : ∃ a b, 1 < a ∧ 1 < b ∧ repunit 4 n = a * b` — supplies the exact factors of the report's table: p ≡ 1 → q(p+1) with q=(p-1)/3; p ≡ 2 → (p-1)(q+1) with q+1=(p+1)/3.
- `prime_repunit_exact (n) : IsPrime (repunit 4 n) ↔ n = 2` and `every_prime_repunit_is_five`.
- `InfinitelyManyPrimeRepunits a := ∀ B, ∃ n, 0 < n ∧ IsPrime (repunit a n) ∧ B < repunit a n` — unboundedness of prime values; since repunit a n is strictly increasing in n, this is equivalent to infinitude both of prime-producing lengths and of distinct prime values (the tex explains this).
- `OriginalClaim := ∀ a, 2 ≤ a → InfinitelyManyPrimeRepunits a`; final `conjecture126_counterexample : ¬ OriginalClaim` (instantiate a := 4).

(i) Definitions faithful. (ii) Counterexample satisfies hypotheses: a = 4 ≥ 2. (iii) Only prime value is 5, so prime values are bounded by 5 — `base_four_not_infinitely_many` refutes unboundedness at B = 5 — direct logical negation of the universal claim. (iv) Not vacuous: the decisive objects (repunits in base 4, primality, all lengths) are present; the compositivity proof is a general symbolic argument ((4^n-1)/3 = (2^n-1)(2^n+1)/3 with 3 dividing exactly one factor), not numerics. My independent python confirms every recorded number. LaTeX matches Lean exactly (same factorization table, same conclusion, same encoding of infinitude).
## Issues found
- Non-blocking: `independent-check.json` has no accompanying script in the package; I reproduced all its rows independently, so the record is accurate.
- Non-blocking: the conjecture's parenthetical (k+1 prime necessary) is not formalized, but the disproof covers all lengths n including prime ones, so nothing depends on it.
## Verdict rationale
A clean, fully symbolic disproof: for a = 4 every repunit of length ≥ 3 factors nontrivially by induction-proved identities, leaving 5 as the unique prime value, contradicting "infinitely many for every a ≥ 2". Build, LaTeX, records, and an independent recomputation of all computational claims all check out; only standard axioms are used.

## Disposition
APPROVED — merged into main (PR 329). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
