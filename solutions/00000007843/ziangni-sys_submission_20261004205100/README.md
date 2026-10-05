# Complete graphs contradict the universal random-greedy size law

For each d >= 2, the actual complete simple graph on d+1 vertices is d-regular. A genuine standard adjacency-based greedy scan returns the first vertex alone for every permutation. Under the actual uniform probability law on all permutations, size is almost surely1 and its Bochner expectation is1.

The asserted benchmark (d+1)log(d)/(d+log(d)) is at least log(d)/2 and tends to infinity. The true relative expected size tends to0 and cannot tend to1, contradicting the unrestricted two-sided1+o(1) clause. The source states no triangle-free or local-tree assumption. The report explicitly distinguishes such restricted results.

Reproduce inside lean/ with Lean 4.19.0:

```text
lake update
lake exe cache get
lake build
```

Mathlib is pinned to c44e0c8ee63ca166450922a373c7409c5d26b00b. The full build prints theorem axiom audits. Actual graph degrees, permutations, recursive greedy output, normalized uniform PMF, probability/expectation and asymptotic limits are proved. Complete report: proof.tex/proof.pdf; both PDF pages were visually checked.
