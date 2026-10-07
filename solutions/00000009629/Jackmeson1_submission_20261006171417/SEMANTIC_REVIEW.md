# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- Minor wording overclaim in the report: "every weaker orbit-preserving notion" should be restricted to notions retaining a bijection of the entire spaces and orbit inclusion at every point. The fixed-point argument does not establish non-equivalence after discarding exceptional points, or for nonbijective orbit-preserving maps. This does not affect the conjecture as explicitly defined.

**Changes made after the review:**

- 'every weaker orbit-preserving notion' restricted to notions that keep a bijection of the whole spaces with orbit inclusion.

**Reviewer notes (verbatim):**

> Accept the disproof under the stated, faithful interpretation of dimension group as Krieger's ordered group, without the distinguished shift automorphism. The full 2-shift and full 4-shift are genuine nondegenerate finite-alphabet edge shifts. Lean explicitly proves their finite-type property and topological mixing in the product/subspace topology. The eventual-range definitions of dimGroup and dimCone give Z[1/2] and its nonnegative cone for both matrices, and DimOrderIso requires an additive equivalence preserving cone membership in both directions. OrbitEquivalent faithfully uses a full-space bijection, Borel measurability in both directions, and equality of the integer-shift orbits. For even the weaker orbit-inclusion hypothesis, the inverse bijection sends each target fixed point to a source fixed point: the image of the source orbit is contained in a singleton. The four constant target configurations would therefore inject into the two constant source configurations, an impossibility. This argument, the dimension computation, and the cylinder-set mixing proof are substantively correct and match the Lean proofs. Although OEDimCriterion has no separate IsSFT premise, its systems are finite-graph edge shifts and counterexample additionally proves IsSFT for both witnesses; there is no out-of-scope counterexample. Falsifying the if direction refutes the first clause and hence the conjunction; abstracting the other clauses as arbitrary propositions in conjecture_false is logically sufficient and does not leave an essential part of this disproof unformalized. Dimension-triple and K^0 interpretations are explicitly distinguished rather than silently substituted. Compilation and the axiom audit are taken as supplied; no substantive LaTeX/Lean mismatch was found.
