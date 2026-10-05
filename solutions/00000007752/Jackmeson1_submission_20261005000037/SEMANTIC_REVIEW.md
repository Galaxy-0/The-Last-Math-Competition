# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- Formal scope limitation: IsBottcherSolution explicitly assumes MeromorphicAt at infinity, and Model.solution_alg uses that hypothesis. The file does not derive it from analyticity and injectivity on an exterior domain, so it does not explicitly formalize the existential formulation with no condition at infinity. The report acknowledges this. Mathematically, univalence rules out an essential isolated singularity, so meromorphic extendibility follows; the missing bridge limits the claimed formal coverage of that variant, rather than invalidating the standard normalized counterexample.
- Square-root notation needs clarification. In (z + sqrt(z^2 - 4))/2, the square root must be the branch asymptotic to z at infinity, namely z times the principal square root of 1 - 4/z^2. It is not the principal square root of z^2 - 4 throughout the exterior domain: at z = -4 those two choices have opposite signs. The report's explicit definition using t and Lean's psi2 use the correct branch; the shorthand formula should specify it.
- The report identifies z^2 - 2 with the standard Chebyshev polynomial T_2. With the usual convention T_2(x) = 2x^2 - 1, the correct identity is z^2 - 2 = 2 T_2(z/2), so these maps are linearly conjugate. This naming error does not affect any calculation or the witness's eligibility.
- The report glosses the Chinese term for single-valued as univalent. Single-valuedness alone does not imply injectivity. The formalization follows the explicit English requirement of univalence and the standard mathematical meaning of a Böttcher coordinate; its coverage should not be advertised as a proof for arbitrary single-valued analytic solutions without additional hypotheses.

**Changes made after the review:**

- The square-root branch is now stated explicitly: the branch asymptotic to z at infinity, z·sqrt(1-4/z^2). It is not the principal root of z^2-4.
- The Chebyshev remark is corrected: z^2-2 = 2·T_2(z/2), a linear conjugacy.
- "Single-valued" is no longer glossed as univalent. The formalization follows the English "univalent" and the standard Böttcher coordinate.
- The formal scope is stated plainly. The unnormalized reading assumes meromorphy at infinity. The variant with no condition at infinity is covered only by a mathematical remark, not in Lean.

**Reviewer notes (verbatim):**

> Accept the substantive disproof, with these minor qualifications. Neither c = 0 nor c = -2 is excluded by the stated conjecture: both are algebraic and have bounded critical orbits, proved for every iterate in bounded0 and bounded2. Being classical exceptional cases does not create an unstated exclusion. IsBottcherCoord faithfully expresses the standard normalized coordinate as a germ near infinity using actual complex analyticity, injectivity, the functional equation, and the asymptotic normalization. coord0 and coord2 prove existence, and Model.coord_unique proves uniqueness near infinity. The unnormalized meromorphic formulation is also genuinely refuted for both coordinate quantifiers, using a proved classification argument rather than assuming algebraicity. The rigidity, quadratic-root, growth, and algebraicity arguments in the report agree with the Lean proof. exists_big and refute produce algebraic counterexamples beyond every proposed radius, so there is no finite-sampling or eventual-quantifier gap. Consequently conjecture_7752_false negates the first clause conjoined with any second clause under the standard reading. Clause2 selects one interpretation of the ambiguous independence wording, but its algebraic ratio z/psi2(z) defeats that interpretation, and the main disproof does not depend on it. Compilation and the stated axiom audit are taken as supplied.
