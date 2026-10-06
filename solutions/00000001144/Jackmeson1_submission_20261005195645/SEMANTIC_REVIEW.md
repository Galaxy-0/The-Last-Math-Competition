# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- The opening report says the witness has 'all three values at most 19/10', including ordinary limits. RateBound and disproof establish the two limsup bounds and rule out convergence to 2; they do not establish existence of either ordinary limit. The report should say that any such limit is at most 19/10, or supply a convergence argument. This is a minor overstatement of the formalized result: nonconvergence to 2 already refutes the claimed limit value.
- The ancillary numerical discussion states that BFS gives sphere ratios tending to the plastic number, calls the upper-bound and supremum readings 'false numerically', and reports an exact sphere formula for the all-minus-two example after numerical checks only. Finite BFS alone proves neither asymptotic convergence nor an all-length formula. These statements need mathematical justification or wording as numerical evidence; the sphere formula also needs k >= 1. The report explicitly excludes these computations from the Lean disproof, so this does not undermine the main result.

**Changes made after the review:**

- Opening claim: now says both limsups are <= 19/10 and any existing limit is <= 19/10; limits are not claimed to exist.
- Numerical remarks (plastic-number ratios, K4 ~2.303, 3*2^(k-1) formula for k>=1) reworded as finite-BFS evidence only.

**Reviewer notes (verbatim):**

> The universal reading with respect to the simple reflections is faithful, and a symmetric rank-three counterexample suffices even if the conjecture includes more general Kac-Moody algebras. FF is a genuine hyperbolic GCM: its graph is connected, its determinant is -2, its quadratic form takes both signs, and every proper principal restriction is positive semidefinite. Its connected proper subdiagrams are A1, A2, and affine A1, so the absence of a general Lean equivalence with the finite/affine-subdiagram definition creates no counterexample-specific semantic gap. The reflection matrices implement the standard simple-root action; nonsingularity also avoids a missing complementary Cartan-space action. The balls and spheres are the actual word-metric sets in the generated matrix group, and weyl_eq_iUnion_ball proves exhaustion. The custom reduced words need not be geodesic or unique: ff_reduce supplies representatives without increasing length, which is sufficient for an upper bound. The counting induction, the bound 13(k+1)(5/3)^k, and its eventual comparison with (19/10)^k are valid. Ball finiteness implies sphere finiteness, while nonnegativity and the eventual upper bounds make the real limsups meaningful. Thus the main theorem proves growthRate FF != 2 and ballGrowthRate FF != 2 and excludes both root sequences tending to 2. The core LaTeX argument matches Lean. Neither an identification with PGL_2(Z), an exact plastic-number growth rate, nor the discarded rank-two example is needed. Compilation and the permitted axiom audit are accepted as supplied in the task.
