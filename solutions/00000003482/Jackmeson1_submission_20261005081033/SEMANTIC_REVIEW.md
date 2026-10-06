# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- The title states the stronger conclusion that the maximal gap is linear in n, whereas the displayed arguments and Lean theorems establish a linear lower bound along n = 5t and exclude every sublinear upper bound. A full M(n) = Theta(n) statement additionally needs an all-n argument: pad the witness with isolated vertices to obtain M(n) >= floor(n/5)/2, and use chi_f(G) >= 0 and chi(G) <= n for the upper bound. These elementary steps are not explicitly supplied; this does not affect the disproof of the conjecture.

**Changes made after the review:**

- The title no longer says the maximal gap is "linear in n". It now states only what is proved: the gap is at least n/10 along n = 5t, so it is not of order n/(log n)^2. The summary also notes that a full M(n) = Theta(n) claim, which would need padding with isolated vertices and the bound chi <= n, is neither made nor needed.

**Reviewer notes (verbatim):**

> Accept the disproof. Reading the unqualified maximal-order clause as a claim about the maximum of chi(G) - chi_f(G) over all n-vertex graphs is faithful; refuting its O(n/(log n)^2) consequence suffices to refute the conjunction. The fractional-colouring definition is the standard independent-set covering LP, with a nonempty feasible set and objective bounded below by zero. Chromatic numbers are finite on these finite graphs, so conversion from ENat is legitimate, and maxGap is a genuine maximum over a finite nonempty graph class. The join construction and relabelling are faithful. Disjoint colour palettes give chi >= 3t, and the independent-pair weighting gives chi_f <= 5t/2, hence maxGap(5t) >= t/2. The asymptotic argument correctly turns any proposed sublinear upper bound into a contradiction along this unbounded subsequence. The logarithmic comparison tends to zero relative to n, so the Big-O, Theta, and asymptotic-equivalence refutations follow. The report's main disproof matches the Lean source; neither the Kneser/Mycielski existence clause nor a classification of extremizers must be separately refuted.
