# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- Minor clarification in the SPECIFIC QUESTION, not a defect in the characteristic-zero theorem: the parenthetical 'in char p <= d the map is not injective' is too broad. For a one-dimensional V, the basis tensor b^(tensor d) maps to X^d, so the restricted map is an isomorphism in every characteristic and degree. Even for dimension two, d = 3 in characteristic 2 gives orbit sizes 1, 3, 3, 1, all nonzero in the field, and hence an injective map. Say instead that injectivity can fail when p <= d; for example, in degree p and dimension at least two, the nonzero symmetric orbit sum with p-1 copies of b_1 and one copy of b_2 maps to p X_1^(p-1) X_2 = 0. The report itself merely excludes other characteristics, which is correct.

**Changes made after the review:**

- Review question wording corrected (injectivity can fail when p <= d; example given). The package itself only claims characteristic 0.

**Reviewer notes (verbatim):**

> Accept under the explicitly stated finite-dimensional, characteristic-zero reading. TPow is a genuine tensor power, permAct is factor reindexing, and symTensors is precisely the invariant subspace. The map toPoly is induced by the product of the basis-coordinate linear forms, and eval_toPoly establishes its diagonal-evaluation interpretation on V*, avoiding any confusion between V and its dual. The main theorem genuinely proves homogeneity, bijectivity of the linear restriction, multiplication compatibility for the averaging symmetric product, and compatibility of the inverse with products. The report's coordinate-orbit argument is sound: invariant coordinates are constant on content classes, each relevant class is nonempty, and its cardinality is invertible in characteristic zero. The normalized orbit sums therefore give the claimed preimages of monomials. The product proof and its normalization agree with tmulL, symz, and symProd. All natural-number degrees are quantified, including zero; the empty tensor product and empty product give scalars and constants. Only the averaging normalization is covered, and finrank_symTensors proves equality of finranks, not the binomial dimension formula. Reading the vague closure clause as linearity and multiplication is reasonable and explicitly disclosed; no other interpretation or arbitrary-characteristic theorem is established. There is no substantive LaTeX/Lean mismatch. Compilation and the permitted axiom audit are taken as stipulated in the review instructions.
