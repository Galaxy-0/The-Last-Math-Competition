# Solution Review — Conjecture 00000000172 (PR 721)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005145918`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (EN+CN): σ = lim σ_n^{1/n} with σ_n = σ_{n−1} + σ_{⌊n/2⌋}, σ₁ = 1; claims: density of 1's in the binary expansion of σ diverges, counting function Θ(log log n), explicit irrationality path. `conjecture.md` byte-identical to the official file.
- LaTeX: independent `latexmk` rebuild exits 0; shipped PDF (xdvipdfmx) matches my pdfTeX rebuild in content; only glyph-extraction artifacts (√ vs q, ∑ vs P from cmsy fonts).
- Lean build: exit 0, 8708 jobs, zero errors/warnings.
- Forbidden content: none (grep clean; `lean/Axioms.lean` is only `#print axioms`).
- Axioms: my independent `CheckJ6.lean` over all 13 theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: `verification/` logs verified; the single manifest "failure" (`conjecture.md`) is a CRLF artifact — hashes match the CRLF variants exactly.
- Sanity check: computed the recurrence numerically — σ_n^{1/n} → 1 (1.405 at n=10, 1.122 at n=100, 1.026 at n=1000), confirming σ = 1 as proven.

## Semantic audit
The conjecture defines σ by its own recurrence, and the submission takes that definition literally (both language versions agree; the report explicitly notes that the name "Somos's constant" usually refers to a different constant ≈ 1.6617 from the quadratic recurrence, and that nothing here concerns that number — an honest and correct scope statement). `IsSomosSeq a` is exactly a₁ = 1 ∧ ∀ n ≥ 2, a n = a (n−1) + a (n/2) (Nat division = ⌊n/2⌋), and `A` (OEIS A033485) witnesses non-vacuity.

The core theorem `tendsto_root` proves, for every such sequence, a_n^{1/n} → 1, via a_n ≤ n·a_{⌊n/2⌋} ≤ n^{⌊log₂ n⌋+1} (monotonicity + induction using Nat.log_div_base), so 0 ≤ log a_n / n ≤ ((log n)²/log 2 + log n)/n → 0. This is the whole disproof: by uniqueness of limits, the conjecture's σ equals 1. The main theorem `conjecture_172_false` then derives the negation of every clause: σ = 1, ¬Irrational σ, and for every binary expansion (m, d) of σ and every real offset c (covering any counting convention for the integer part), the counting function c + #{k < n : d k = 1} is (i) not Θ(log log n) (Mathlib `IsTheta`), (ii) of convergent ratio, and (iii) not tending to +∞. The key lemma `expansion_of_one` (the only binary expansions of 1 are 1.000… and 0.111…, with the subtle 0.111… case handled by a nonneg-term summability argument) is correct.

Quantifier structure: the conjecture is a conjunction of three claims; the Lean theorem establishes the negation of each conjunct, hence the exact negation of the whole. The tex's scope remark fairly notes that the reading "number of 1's tends to infinity" alone is not refuted for the 0.111… expansion, but that expansion is eliminated jointly with clause (i), which fails for every expansion — so the conjecture as written (a conjunction) is false regardless.

## Issues found
- None blocking. (The SHA-256 manifest again stores CRLF hashes — cosmetic, content verified.)

## Verdict
APPROVED. The mathematics is correct (σ = 1 follows from the elementary bound a_n ≤ n^{⌊log₂ n⌋+1}; verified numerically), the formalization is faithful to the written definition, the negation is exact, and the build/axiom/audit trail is clean.
