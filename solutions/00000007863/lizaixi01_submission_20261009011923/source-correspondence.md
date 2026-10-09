# Source correspondence for 00000007863

The exact original SHA256 is 055b0710d93405331ed765147d4deef11a9f4a20f3aa74dca984dcbdf6ba72e2. Both copied source files retain those bytes. Both languages define expected randomized value-oracle query complexity for normalized monotone submodular maximization under |S|<=k and assert q(n,k)=Theta(n), an exact constant-one lower bound/every point queried, followed by an improved-approximation jump and exponent explanation.

## Domain and necessary lower-bound target

The source supplies no k<n restriction, fixed-k asymptotic, budget ratio separated from one, or singleton-query requirement. This package uses the allowed sequence k=n with n unbounded. A uniform Theta(n) law on the stated budget domain entails an eventual positive linear lower bound on this sequence. A linear lower bound for all randomized algorithms entails the same necessary assertion for the legitimate deterministic/singleton-seed subclass formalized here. The premise-free counterexample rejects that assertion.

The output is a feasible set satisfying the objective approximation, the standard maximization convention. The source does not require separately reporting the set's unknown objective value. A different output requirement, k<n exclusion or fixed-k-only asymptotic would be a revised claim; this package does not silently insert such restrictions and requires independent semantic review of the disclosed scope.

## Exact actual objective class

Ground n is Fin n. Actual subsets are Finsets, and SourceObjective.value is a real-valued set function on them. `normalized` means value(empty)=0; `monotone` is monotonicity for the actual subset order; `submodular` is value(A union B)+value(A intersection B)<=value(A)+value(B). No optimum scalar, probability of success or lower-bound axiom is assumed. The standard normalized convention is explicit rather than left implicit.

`feasibleValues f k` is the actual set of values of subsets with cardinality at most k. `univ_feasible` proves card(univ)<=n. `univ_optimal` proves IsGreatest of feasibleValues f n for EVERY objective, using its actual univ value and subset monotonicity. `objective_nonnegative` derives nonnegative values from normalization and monotonicity. `approximationRatio` is exactly 1-1/Real.exp 1, with positivity and upper bound one proved. `approximation_at_univ` proves that factor times every competitor's objective is at most the returned univ value.

The source's submodularity is retained but unused in the stronger all-monotone proof. This does not enlarge the original hypotheses to simplify a selected objective. `cardinalityObjective` witnesses nonemptiness and has actual ground-set value n; for n>0 it is nonconstant. It is auxiliary evidence, not the whole counterexample family of functions.

## Actual oracle interaction and random expectation

`ValueProgram` has return-set nodes and query-set nodes with real-answer continuations. `run` evaluates against the actual oracle value function, supplies its queried real answer to the continuation, and increments query count by one at each query node. `fullSetProgram n` is the same return-univ program for every oracle. `fullSet_run` proves its actual output is univ and its query count is zero. Neither the cost nor its connection to the program is an added premise.

`ValidApproximation n k P` quantifies over ALL source objectives, requires actual interpreted output feasibility, and compares its value with every actual feasible set. `fullSet_valid` proves that property at budget n; `fullSet_uniform_zero_cost` gives a uniform zero upper cost across the whole class. This defeats the worst-case-over-functions lower bound rather than demonstrating only an easy f=0 input.

The actual singleton seed Fin 1 has mass one, proved nonnegative and normalized. `expectedQueries` is the finite mass-weighted sum of the actual interpreted query count for the seed-indexed program. `singleSeed_expected_eq_cost` and `fullSet_expected_zero` prove the expectation/cost connection and zero expectation for every objective. A deterministic exact optimizer is allowed regardless of whether randomized approximation is conventionally measured in expectation or by success probability.

`UniversalExpectedLowerBound` states the necessary lower-bound assertion on this one-seed protocol subclass: every all-objective valid protocol must have some source objective with expected cost at least C. The source's broader randomized lower bound would imply it. The definition is not presented as a full randomized complexity model or a definition of q(n,k). `no_positive_full_budget_expected_lower_bound` rejects it for any C>0. `no_eventual_linear_expected_lower_bound` rejects every eventual c*n comparison along (n,n), using eventually n>=1, so the argument is genuinely asymptotic.

## Final certificate and untouched clauses

`full_budget_counterexample` has no hypotheses. It conjoins actual ground-set cardinality, cardinality-objective nonvacuity, exact approximation coefficient, normalized seed mass, all-n/all-objective output feasibility and greatest-value optimality, actual interpreted return/cost, expected zero queries and the asymptotic lower-bound contradiction. These are proofs about concrete source objects and an actual protocol, not assigned arithmetic values.

The greedy upper-bound claim, improved (1-1/e+epsilon) approximation jump, doubly logarithmic exponent and asserted information-theoretic duality are not individually formalized or proved false. Their epsilon/domain conventions are omitted in the source. A false necessary unrestricted-budget lower-bound conjunct refutes the original conjunction on the disclosed reading; it does not settle every separate statement.

## Provenance and acceptance boundary

The root identified the k=n route, and run7863-scout-v1 supplied the sealed compiled core used here (result SHA256 12fa9e646fe069d8f39b2528c698420e1ecba2270984c1d9a1b968dba021c2b0). This author adds the full certificate, nonconstant witness and explanatory package. No first/new-mathematics claim is made. Public package caches are read-only; the author emits only owned Main.olean output. Parent-owned private dependencies, fresh replay, gate receipts and independent semantic/PDF review remain required for acceptance.
