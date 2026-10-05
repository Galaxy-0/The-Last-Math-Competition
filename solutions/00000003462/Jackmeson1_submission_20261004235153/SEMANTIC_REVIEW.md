# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- Minor terminology/definition mismatch: IsDoublyCriticalEL omits connectedness, which the report's quoted standard definition requires. For example, K6 together with an isolated vertex satisfies this Lean predicate but is not connected. Thus this predicate is not exactly the standard class. This does not undermine the refutation: the actual witness K6 is connected and satisfies the standard double-critical condition.

**Changes made after the review:**

- `IsDoublyCriticalEL` now requires connectedness, which the standard Erdős–Lovász definition includes. The witness K6 is connected, so the refutation is unchanged.

**Reviewer notes (verbatim):**

> The English and exact-one-drop Chinese definitions are faithfully represented using Mathlib SimpleGraph, chromaticNumber, induced vertex deletion, and edge deletion. K6 has chromatic number 6, is edge-critical, leaves K4 after deleting any two distinct vertices, and has 15 > 28/3 edges. It therefore refutes the English upper bound and the standard double-critical upper bound, but is correctly not claimed as a Chinese-class witness. The report's general counting proof is correct: nonisolated vertices have degree at least 5, the English deletion property permits at most one isolated vertex, and v >= 6. Consequently 2e >= 5(v-1) implies 3e > 5v+1, or e > (5v-2)/3 + 1. This excludes exact attainment and both integer roundings throughout EN and its subclass ZH. The Lean statements and proofs capture these arguments, with no substantive LaTeX/Lean mismatch. In ordinary mathematical usage, 'the improved bound uniquely attained by ...' asserts attainment as well as restricting its achievers, so BoundAttained is a faithful necessary clause and its negation refutes the Chinese conjunction even without proving the class nonempty. If that wording were instead weakened to the purely conditional 'equality implies KY', the submission would not establish that the Chinese upper bound alone is false; it explicitly relies on the stated attainment assertion. Quantifying over arbitrary KY predicates and girth clauses is legitimate because a necessary conjunct already fails. The lower-bound variant is likewise refuted only through attainment; its inequality is correctly proved true. K6 can fairly be called an elementary or trivial counterexample, but it is an admissible graph under the written English and standard hypotheses, which do not exclude complete graphs. The formalization proves actual graph-theoretic facts, not vacuous arithmetic.
