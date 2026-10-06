# Semantic review (independent, pre-submission)

An independent model reviewer (GPT-6 Astra, reasoning effort "xhigh", separate session) received the exact conjecture text, the full LaTeX report, the full Lean source and a reviewer checklist distilled from 93 closed-unmerged pull requests of this competition. It was asked whether the Lean main theorem settles the conjecture as written, whether the reading is faithful and not a loophole, whether the Lean definitions are faithful to the standard notions, whether the mathematics is correct, and whether report and Lean match. This is an automated review prepared by the submitter, not the competition's maintainer review.

**Verdict:** accept = True; severity = minor; reading faithful = True.

**Issues raised (verbatim):**

- Minor degree imprecision in the report's 'Readings not refuted' paragraph (b): the first coordinate of g_K has degree K-1 in z, but the polynomial map itself has degree max(1, K-1), since its last coordinate is z+1. In particular g_1 has degree 1, not 0. This does not affect the unbounded-degree observation or either counterexample.

**Changes made after the review:**

- (b): the degree of g_K is max(1, K-1), not K-1.

**Reviewer notes (verbatim):**

> Accept as a disproof of the specified unrestricted upper-bound reading R1, and consequently of the equality reading R2. The Definition line's description of DML as 'finiteness of intersections' is inaccurate as a general description: arithmetic progressions of return times are compatible with the DML setting. It does not explicitly impose a finite-intersection hypothesis on the subsequent conjecture. The concrete map f is even an affine automorphism. Its subvariety being invariant under f^2 therefore does not exclude it from the stated class; there is no stated prohibition on periodic subvarieties or instruction to discard their return times. If finite intersections were instead imposed as an additional hypothesis, the main witness would not qualify, and this acceptance would not extend to an eventual upper-bound claim with that restriction.
> 
> The Lean definitions faithfully represent polynomial maps on rational affine space, actual function iterates, finite sets of distinct orbit points, and hitting times. The orbit formula and injectivity from the z-coordinate ensure that counting repeated visits is not being substituted for counting distinct intersection points. The zero-locus equations, their total degrees, the prime vanishing ideal, and the coordinate-ring and ambient Krull dimensions genuinely certify the codimension-r affine line. The restriction map to Q[z] justifies those geometric certificates. The formal main theorem quantifies over every real polynomial and negates an eventual bound, using the genuine estimate P(log N) <= N/4 eventually and the lower bound N/2 for the count. This proves the required asymptotic obstruction rather than merely checking finitely many iterates.
> 
> The second family's return times are exactly 0,...,K-1, including the K=1 empty-product case. Its injectivity and eventual count K are correctly established. The infinitely many distinct positive logarithms force any eventual equality polynomial to be the constant K. The uniform-bound contradiction correctly chooses K=N+1 after choosing N. Its quantifiers are essential: it excludes a single P valid for all K and all N>=1, but not a fixed P valid eventually for each K with a K-dependent threshold. Indeed P(T)=T^r eventually bounds every finite total, even with coefficients independent of the map and starting point. Thus this family does not repair the main argument if a finite-intersection, orbit-dependent eventual-threshold interpretation is imposed. The report explicitly states the all-N scope of R3; the Lean theorem matches that scope. Apart from the minor degree wording, the report's mathematical arguments are correct and sufficiently complete, with no substantive mismatch with Lean. Compilation and the permitted axiom audit are taken as stipulated in the input.
