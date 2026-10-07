# Solution Review — Conjecture 00000000037 (PR 670)

**Submission:** Jackmeson1 — `solutions/00000000037/Jackmeson1_submission_20261005100008`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (English + Chinese); `conjecture.md` byte-identical to the official file.
- **LaTeX report:** read in full; independently rebuilt with `latexmk` — exit 0.
- **PDF match:** normalized text of shipped vs. rebuilt PDFs differs only in math-glyph extraction artifacts (∈→2, ⊆, ≤, braces). Content identical.
- **Lean build:** `lake build` succeeded, 8708 jobs, zero errors, zero warnings.
- **Axioms:** independent scratch `Check.lean` for `conjecture_37`, `conjecture_37_littleO`, `conjecture_37_firstPrimes`, `sidon_upper`, `et_sidon`, `construct`: all exactly `[propext, Classical.choice, Quot.sound]`.
- **Cheating scan:** clean (no `sorry`, `native_decide`, `axiom`, `set_option`, metaprogramming).
- **Auxiliary code:** none shipped; the proof needs none (π is Mathlib's `Nat.primeCounting`, Bertrand and Chebyshev bounds are Mathlib theorems).
- **Semantic audit:** pass (see below).
- **Sources:** the Sidon definition matches the cited Wikipedia page; only the submission folder is added; metadata marks the conjecture unsolved.

## Semantic audit

The conjecture states: "Among the primes there exists a Sidon set of size (N/log N)^{1/2−o(1)}." The parameter N (unbound in the sentence, with N/log N ~ π(N)) most naturally bounds the primes; the literal reading — for all large N there is a Sidon set of primes ≤ N of size (N/log N)^{1/2−o(1)} — is exactly what is formalized, in three equivalent forms: the ε-form (∀ ε > 0, eventually (N/log N)^{1/2−ε} ≤ |A_N| ≤ (N/log N)^{1/2+ε}, with every element of A_N prime and ≤ N), the literal δ(N)-form (δ(N) → 0 and |A_N| = (N/log N)^{1/2−δ(N)}), and the "first N primes" form. The Sidon definition (a + b = c + d forces {a,b} = {c,d} as multisets) matches the standard one. Since the conjecture as written asserts an existence statement per size parameter, and the submission proves that statement with both the lower bound and the matching universal upper bound, the proof establishes exactly the claim; no hypothesis was strengthened and no definition weakened.

The proof is a complete and correct adaptation of the Erdős–Turán/Ruzsa polynomial construction to the primes. (1) For an odd prime p, e(k) = 2pk + (k² mod p), k < p, is injective with distinct pairwise sums: from e(k₁)+e(k₂) = e(k₃)+e(k₄), dividing by 2p (residues lie in [0, p)) yields k₁+k₂ = k₃+k₄ and r₁+r₂ = r₃+r₄; modulo p this gives k₁+k₂ ≡ k₃+k₄ and k₁²+k₂² ≡ k₃²+k₄², whence 2(k₁−k₃)(k₁−k₄) ≡ 0 in Z/p, and p odd gives the multiset equality (Lean proves this in ZMod p). (2) Shifts into primes: for each k < p, every prime q ∈ [2p², L] yields a shift b = q − e(k) ∈ [0, L] with e(k)+b prime; double counting gives Σ_{b≤L} #{k<p : e(k)+b prime} ≥ p(π(L) − 2p²), so some shift captures at least the average (Lean: `exists_shift`, with truncated ℕ subtraction handled correctly). (3) Choosing p via Bertrand with m = ⌊√(⌊x/16⌋)⌋, x = π(N/2) ≥ 64, gives 4p² ≤ x < 16p², elements ≤ 2p² + N/2 ≤ N, and c = |A| ≥ p·x/(2N); hence x³ < 16p²x² = 16(px)² ≤ 64N²c² (Lean: `construct`). (4) Chebyshev (Mathlib `Chebyshev.pi_ge`) gives π(N/2) ≥ 4N^{1−η} eventually (Lean: `pi_lower`, using log x = o(x^η)); with η = 2ε′/3, x³ ≥ 64N^{3−3η} then forces c² > N^{1−2ε′}, i.e. |A_N| > N^{1/2−ε′} ≥ (N/log N)^{1/2−ε′}. (5) The matching upper bound is the standard difference-injection: |A|² − |A| ≤ 2N for any Sidon A ⊆ [0,N], and 2√N ≤ (N/log N)^{1/2+ε} eventually (Lean: `sidon_upper`). I re-derived each inequality independently; all are correct, and the exponent bookkeeping (ε′ = min(ε, 1/2), N/log N ≥ 1, log N ≥ 1) is sound.

Two faithfulness points deserve emphasis. First, this is a finite-set statement per N, which is what the sentence says ("exists a Sidon set of size …" with the size parameterized by N); the genuinely famous open problem — an infinite Sidon set of primes with counting function > x^{1/2−o(1)} — is a different, stronger statement that the text does not assert; the report flags it explicitly as not covered. Second, the proof gives the sharp order: |A_N| ≍ √N/(log N)^{3/2} = (N/log N)^{1/2}/log N = (N/log N)^{1/2−o(1)}, and `sidon_upper` shows the exponent 1/2 cannot be improved — so the submission neither over- nor under-claims.

Sanity check: for p = 5, e(k) = 10k + (k² mod 5) gives {0, 11, 24, 34, 41}; all 15 pairwise sums (with repetition) are distinct. The same holds by direct enumeration for p = 11 (66 sums).

## Issues found

- The reading "of size (N/log N)^{1/2−o(1)}" as a family of finite sets (primes ≤ N) rather than an infinite set with counting-function lower bound is the crux; it is the literal reading of the sentence in both languages, is argued transparently in the report, and is corroborated by the matching universal upper bound for finite Sidon sets. The infinite reading is explicitly listed as not covered.
- Minor: the abstract says "Erdős–Turán Sidon set"; the construction with the shift is the classical Ruzsa-type adaptation. No mathematical content turns on the attribution.

## Verdict

APPROVED. A complete, fully formalized proof of the conjecture as literally stated, with the strong ε-form, the literal δ(N) → 0 form, and the first-N-primes form all proved from faithful definitions; the build and independent axiom audit are clean, and I independently re-derived every inequality in the chain.
