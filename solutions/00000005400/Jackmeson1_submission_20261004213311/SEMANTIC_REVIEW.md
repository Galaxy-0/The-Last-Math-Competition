# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- Minor LaTeX/Lean convention mismatch: the report defines the least period as a least positive return time, without assigning a value when no such time exists, but subsequently asserts equality of least periods for every point. Lean's Function.minimalPeriod is zero at nonperiodic points. State that convention explicitly, or restrict the prose equality to periodic points. This does not affect the disproof.

**Changes made after the review:**

- The minor issue was a convention mismatch. The report now states the least-period convention explicitly: the least positive n with f^n(x) = x, and 0 for non-periodic points. This is exactly Mathlib's `Function.minimalPeriod`, so the pointwise equality of least periods holds at every point.

**Reviewer notes (verbatim):**

> The submission refutes the literal conjunction under the standard pointwise meaning of conjugate maps: a bijection intertwining the two maps everywhere. The Lean proof is substantive and unrestricted by finiteness. It transports all iterates, periodic-point sets, exact-period sets and periodic cycles, proves equality of their cardinalities and of period sets, and preserves minimal periods at corresponding points. These are faithful periodic notions. The report's transport argument matches the formalization and is mathematically correct, apart from the minor convention issue above.
> 
> Leaving orbit-distribution and same-measure conditions as arbitrary predicates is legitimate here: the required conjugate pair with different periodic data is already impossible without either condition. Allowing the separating pair to be independent of the first pair weakens the existential assertion, so disproving that weaker assertion also disproves the literal same-pair requirement. Including period zero in PeriodDataDiffer similarly causes no gap. This is not merely finite evidence or a prose-only refutation.
> 
> The earlier objection is not mathematically justified against the literal pointwise-conjugacy conjunction: disproving a required final conjunct disproves the whole claim. The theorem does not disprove the first existential clause considered alone, and the report correctly acknowledges this. A reviewer could nevertheless repeat a reading objection if the final clause is treated as nonbinding explanatory language, or if conjugacy is intended in the also-standard ergodic-theory sense modulo null sets. Such a conjugacy can ignore periodic points on null sets, and neither arbitrary side predicates nor the measured_conjugate_same_periods theorem remove its explicit everywhere-intertwining hypothesis. The report expressly distinguishes that alternative. Thus acceptance is warranted for the supplied literal pointwise reading, not a guarantee that the reviewer will adopt that reading; acceptance of the sibling submission is not itself mathematical evidence.
