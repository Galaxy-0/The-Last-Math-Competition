# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- The Reading paragraph says the parenthetical uniqueness assertion "is implied by, and fails with, the main clause." This is unjustified: showing that a particular map is APN does not establish uniqueness among APN functions, and failure of this map to be eventually APN does not resolve an independent uniqueness assertion. Replace this with a statement that the explicit differential-uniformity clause is refuted and no separate uniqueness claim is established. This does not undermine the main disproof.

**Changes made after the review:**

- The Reading paragraph no longer says that the parenthetical uniqueness assertion is implied by the main clause and fails with it. It now says the uniqueness assertion is separate and is neither used nor refuted. Only the explicit differential-uniformity clause is refuted, and that already makes the conjunction false.

**Reviewer notes (verbatim):**

> The usual reading of "for large q" as an eventual universal assertion is faithful. The Lean definitions use the actual power map and the standard maximum of differential solution counts over nonzero increments. The inverse identity is applied only where q >= 3, and divisibility by 3 forces q >= 4. The four distinct witnesses 0, -1, omega, omega^2 at increment 1 and target 2 are valid in both even and odd characteristic. The formalized families q = 4^k and q = 7^k give unbounded counterexamples, and the three not_eventually_two theorems establish the corresponding negations rather than merely checking finitely many cases. The cardinality and exponent versions of the characteristic-2 threshold are equivalent. The odd-order extension is correct and does no harm. Apart from the peripheral uniqueness sentence, the report and Lean agree and the mathematical argument is complete. Restrictions to odd binary exponents or powers of 3 are not present in the stated conjecture and are explicitly excluded from the submission claims.
