# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- Minor scope ambiguity in the report's Reading paragraph: 'The only graph on which the claimed tightness holds is the order-zero graph K_0' should say 'the only complete graph'. As a statement about all graphs, it is false: G = C_4 has complement 2K_2, with mu(2K_2) = 1 = 4 - omega(C_4) - 1. This does not affect either counterexample family or the disproof.

**Changes made after the review:**

- The reading paragraph now says that among complete graphs the claimed tightness holds only for K_0. Read as a claim about all graphs, the old sentence was false: C_4 has complement 2K_2 with mu = 1 = 4 - omega(C_4) - 1. The counterexample families and the disproof are unchanged.

**Reviewer notes (verbatim):**

> The Lean main theorem substantively refutes the literal inequality. IsCdVMatrix faithfully encodes the standard real symmetric matrix conditions, counts negative eigenvalues with multiplicity, and imposes the Strong Arnold Hypothesis on symmetric X. The natural-valued supremum is bounded, and the explicit witnesses establish nonemptiness for every graph used. For complete G, the diagonal witness is admissible and has corank 1 when n >= 2; at n = 1, (-1) is admissible with corank 0. The integer-valued right side is -1, so the claimed complete-graph equality fails. For edgeless G with n >= 2, -J has one negative eigenvalue, rank 1, and automatic Strong Arnold rigidity, giving mu(K_n) >= n - 1 > n - 2. This second family also rules out an objection based on natural-number subtraction or nonnegativity alone. The report's witness arguments agree with the formalization. The K_0 convention is outside the theorem's quantified ranges. Compilation and the stated axiom audit are taken as supplied.
