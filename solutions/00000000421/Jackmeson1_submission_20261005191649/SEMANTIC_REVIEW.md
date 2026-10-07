# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- Minor LaTeX boundary-case omission: the proof of the first corner lemma asserts that (0,r-1) belongs to the diagram without assuming r>0. This fails for the empty diagram, although the lemma itself remains true: its two named corners then coincide at (0,0). State the predecessor claim conditionally on r>0, and likewise on c>0 for columns, or handle the empty diagram separately. Lean's corner_row and corner_col already use the correct conditional hypotheses. All shapes used in the prime-size argument are nonempty, so this does not affect the disproof.

**Changes made after the review:**

- Corner lemma: the predecessor claim (0,r-1) in mu is now conditional on r>0 (and c>0 for columns); the empty diagram is handled.

**Reviewer notes (verbatim):**

> Accept the disproof under the stated uniform-standard-Young-tableau reading, also proved for uniformly chosen size-n Young diagrams. SYT is a faithful inverse-filling encoding: injectivity gives exactly n distinct occupied cells, the lower-set condition gives an ordinary Young diagram, and row_lt/col_lt impose precisely the usual strict increase of entries. Proof fields introduce no counting multiplicity. The definitions E_SYT and E_shape are the corresponding uniform finite averages. addable uses exactly the cells whose insertion preserves the lower-set property; addable_subset and addable_finite ensure that Set.ncard is the actual finite cardinality. The combinatorial argument is sound: nonempty shapes have at least two addable cells, nonrectangular shapes have at least three, and a prime-area rectangle must be a row or column. Row/column uniqueness bounds the exceptional objects by two; the explicit hook supplies an object outside them and makes the averaging denominator positive. Thus the 7/3 bound holds for every prime p>=3. not_limit_two uses arbitrarily large primes, so the conclusion is genuinely asymptotic, and its negated eventual C/log(n) bound rules out the stated rate interpretations. The report's substantive proof matches the Lean theorem, apart from the minor boundary-case omission above. The stronger divergence remark is explicitly unused and unformalized; the finite numerical check is not used to establish the disproof. Plancherel and bounded-entry semistandard distributions are outside the specified uniform-SYT reading and are not claimed as formalized. Compilation and the axiom audit are taken as stipulated in the review instructions.
