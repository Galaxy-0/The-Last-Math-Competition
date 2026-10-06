# Conjecture 00000003479: disproof at the admissible p=1 boundary

Verdict: false as written. Each distinct edge in G(n,1) is present surely,
so the graph is K_n. A proper coloring is injective and uses at least n
colors. For every n>4, the probability of a harmonious coloring with at
most 2 sqrt(n) colors is zero. The relative concentration event with
tolerance 1 is a subset of this impossible event. Its probability tends
to zero, not one. Since log(n)/n <= 1, this contradicts the asserted uniform
law. No single finite anchor or unproved tail estimate is used.

## Semantic coverage

`lean/Counterexample.lean` defines the exact sum-based harmonious coloring
from the problem, on Mathlib's `SimpleGraph (Fin n)`, with an actual proper
`Coloring (Fin k)`. It defines minimum harmonious numbers by attainment
and minimality, not as freely chosen numeric sequences. It proves actual
harmonious colorings exist for every finite graph by constructing the
Sidon labels `(2*n^2+1)*i+i^2`. Equality of endpoint-label sums determines
the endpoint-index sum and square sum, hence the unordered endpoint pair.
It then defines `harmoniousNumber` by natural-number well-ordering and
proves the concentration event is exactly the relative-error event for
this explicit minimum-color-count function.

`GnpOneLaw` is the p=1 edge-marginal law on actual graph-valued PMFs. The
proof `support_is_complete` shows that every graph in the support is the
complete graph; `gnpOne` is its point-mass distribution. Independence is
unnecessary at this boundary, so the zero-probability theorem is valid for
every PMF having the required edge marginals, including standard G(n,1).

The capstone `conjecture_boundary_is_false` negates relative concentration
at p=1. A uniform law on the specified parameter range must include this
boundary; `one_is_admissible` verifies its range condition for all n>0.
The proof does not need a closed formula for the harmonious number. Its
existence, attainment, minimality, and identification with the event's
minimum witness are all proved, and every coloring in the concentration
event is impossible at the complete-graph boundary.

## Earlier submission and its errors

Prior PR #228 was closed after review. Its arithmetic theorem assumed
the coloring count bound, never derived it from a graph/coloring object,
left the Chernoff estimate outside Lean, and used a single n=1000 anchor
which cannot refute an asymptotic law. Its discussion also used the usual
unordered-color-pair convention, not this problem's endpoint-sum wording.
This submission replaces that strategy with the exact sum-based object,
a graph-valued probability law, a coloring-derived injection bound valid
for every n, and a formally proved failure of the relative concentration
limit. The prior numeric certificate is not used.

## Reproduction

From `lean/`, run `lake update`, `lake exe cache get`, and `lake build`.
Lean 4.33.1 and Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474` are pinned.
The capstone and supporting probability/range theorems print their axiom
dependencies during the build. They use only `propext`, `Classical.choice`,
and `Quot.sound`.

The report is `solution.tex` and its compiled PDF is `solution.pdf`.
No exhaustive or randomized numerical computation is required.
