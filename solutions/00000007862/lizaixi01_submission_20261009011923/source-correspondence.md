# Exact source correspondence for 00000007862

The exact original SHA256 is 53ded20d62b695f89efa5391da50d5c20e77e7746a90c5919dd63a38ee367ce0. Both copied source files retain those bytes. The source is bilingual, with matching mathematical content: expected restart rounds T on a variable-event hypergraph, the displayed upper bound, a quadratic divergence assertion for that bound as e*p* tends to 1, a branching exponent explanation, and a claimed adaptive exponent reduction.

## Necessary conjunct selected for disproof

Both languages identify the displayed bound itself as the object of the quadratic divergence law. The formal target is that unqualified law when asserted universally for admissible instance families. A positive quadratic asymptotic coefficient or a Theta inverse-square law entails an eventual lower comparison c/(1-e*p*)^2 <= B for some c>0. `actual_no_positive_quadratic_lower_bound` excludes every such comparison on the actual family. This is stronger than excluding one proposed coefficient; it directly addresses both usual meanings of an exponent-2 divergence law.

The source contains no worst-case supremum, growth rate of event count, exclusion of singleton events, or special scaling of product(1-p_i). We do not silently invent those qualifiers. If independent semantic review requires an existential or growing-family reading, this package does not settle that revised claim and must not be accepted as such. The displayed bound still has the proved first-order behavior on the permitted singleton family.

## Actual probabilistic instance

`FiniteLaw` records a nonnegative real mass at each outcome and a proved finite total 1. This is an actual finite probability space: the probability of an event is the sum over its outcomes. No probability scalar or expectation equality is supplied as a premise.

`Outcome=Fin 2`, `Variable=Fin 1`, and `Event=Fin 1`. `variableValue` maps the outcome to its sole variable value. `eventFamily` is the subset {0}, and `eventVariables` is the singleton variable support. `event_depends_on_its_variables` proves that equal values on the support give equal event membership. `instanceLaw n` is the Bernoulli law with p_n=(1-1/(n+2))/exp(1), derived from internal admissibility proofs. `eventProbability n i` sums the actual law on the actual subset and is proved equal to p_n.

`pStar n` is the sole event probability. `pStar_largest` proves `IsGreatest (Set.range (eventProbability n)) (pStar n)`: the maximum belongs to the range and bounds every event probability. It is not assumed to be largest. The finite sum and product use Event=Fin 1, exactly one real bad event.

`dependencyAdj i j` means i and j are distinct and their actual variable supports overlap. It is symmetric, irreflexive and has no edges; `dependencyDegree` counts the actual adjacent vertices and is proved zero. `distinct_event_independence` is vacuous for distinct events because there is only one actual event. This is the legitimate singleton case of event dependency, not an impossible hypothesis added to the counterexample certificate. The usual symmetric LLL condition exp(1)*pStar*(d+1)<1 follows from the constructed p_n. The original omits such a degree condition; the example satisfies it anyway.

## Actual displayed bound and asymptotics

`actualBound n` is defined as (sum i,eventProbability n i)/((1-exp(1)*pStar n)*(product i,1-eventProbability n i)). It is not defined as an unrelated scalar surrogate. `actualBound_eq_formula` proves the reduction to pStar/((1-exp(1)*pStar)*(1-pStar)); `actualBound_pos` proves it is positive. `gap n` is exactly 1-exp(1)*pStar n and is proved positive. `criticalProduct_tendsto_one` proves the required approaching critical product.

The bridge proves `actual_scaled_square_tendsto_zero` and `actual_scaled_linear_tendsto` with coefficient 1/(exp(1)-1)>0. `actual_no_positive_quadratic_lower_bound` converts the normalized-square limit into the impossibility of every positive eventual inverse-square lower comparison, using positivity of the exact gap. The final premise-free `literal_bound_counterexample` combines actual law normalization/nonnegativity, event probabilities, maximum, bound reduction, dependency degree, admissibility, bound positivity, critical approach, both limits and the lower-bound contradiction. Supporting theorems also record variable support dependence and graph relations.

## Clauses not separately formalized

T, randomized resampling restart rounds, the branching-process survival exponent, and adaptive selection are not defined or assumed in this package. Their generic algorithms and precise probabilistic laws are omitted by the source. This package makes no claims about their individual truth. Refutation of a necessary bound-divergence conjunct refutes the full conjunction under the stated universal interpretation; it does not constitute a proof or disproof of each remaining conjunct individually.

## Provenance and acceptance boundaries

The scalar limit bridge and finite-law core reuse the sealed scout artifact from run7862-scout-v1, explicitly credited. New author work connects actual variable/event supports, dependency adjacency/degree, actual maximum and source-bound expression, and assembles the premise-free final theorem. The source uses only two cached public mathlib imports; missing Probability and SimpleGraph caches are disclosed. The author does not alter public dependencies or claim independent review. Manager-owned clean dependency replay, deterministic gate, independent semantic/PDF review and acceptance remain separate.
