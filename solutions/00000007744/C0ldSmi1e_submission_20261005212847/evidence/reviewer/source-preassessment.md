# Independent source-only preassessment: 00000007744

Prepared on 2026-10-05 before receiving a candidate submission. Inputs read: the exact bilingual conjecture at `/private/tmp/tlmc-next-clean-snapshot-20261005T144418Z/conjectures/00000007744.md` and only the English and Chinese contribution guides at `/private/tmp/tlmc-next-current-refresh-after525-20261005T205636Z-bounded-repair/README.md` and `README.zh-CN.md`. No selector rationale, old solution, old PR, other problem artifact, or external mathematical history was read.

Source identity supplied by coordinator: SHA256 `1813b1549a59216461015e9e66b6397927130922289f542a4f524bc2312e70e4`; Git blob `7d0aa5eaf4ed7df3b8e52db76a9807f1e50c7562`.

## Literal requirements

The setting is the uniform model of random d-regular graphs, with spectral empirical measure tending to the Kesten–McKay law. The asserted second-order object is the joint limiting process of centered normalized trace polynomials multiplied by sqrt(n). The Chinese text explicitly centers `tr p(A)` by its expectation. The conclusion asserts a Gaussian family, a constrained noncrossing-return-path covariance rule, and the particular scalar variance `4 - 12/d + 8/d^2` for `p=q=x^2`, with a claimed limit 4 as degree grows.

A complete disproof may contradict one necessary concrete conclusion, such as the x² variance, without developing or refuting the entire unspecified pairing rule. The ambiguity in the combinatorial description is not itself a mathematical disproof. The source does not specify every normalization, vertex labeling convention, or whether graphs are simple; a report must state and defend its use of the conventional uniform simple d-regular graph model rather than silently changing the random object.

## Independent elementary obstruction

For a finite undirected simple d-regular graph with adjacency matrix B, `(B²)_{vv}` equals the degree d. Thus `Tr(B²)=n*d` and the normalized trace is d. This identity holds graph by graph throughout the entire uniform sample space, not only for one chosen graph. Deterministically rescaling B merely changes this fixed value. Therefore the centered quadratic trace equals zero identically. Multiplication by sqrt(n), or any other deterministic factor, cannot change it. This is insensitive to the ordinary normalized-versus-unnormalized trace convention.

For d=3, the claimed variance is 8/9, whereas the random variable is identically zero and its law is delta_0 for every admissible n. Hence every weak limit of that scalar law is delta_0, with variance zero. Degree 3 supplies a clean positive nondegenerate numerical contradiction. In general the formula is `4*(d-1)*(d-2)/d²`, positive for integer d>=3. Degrees 1 and 2 alone do not disprove the formula.

This obstruction does not require an external central limit theorem, asymptotic cycle counts, a GUE variance calculation, or a proof of Kesten–McKay convergence. Those would enlarge the semantic and verification burden without being needed for this concrete contradiction.

## Critical traps

1. A finite example such as K4 by itself does not disprove an asymptotic distribution claim. The constant-trace identity must apply to the whole uniform ensemble along an unbounded sequence of admissible graph sizes, and the sample spaces must be nonempty.
2. Uniformity must be instantiated on actual d-regular graph sample spaces (or a graphwise universal theorem must explicitly cover that model). A handpicked deterministic graph measure or a synthetic zero random variable is not a substitute for the source model.
3. One cannot infer the variance of a weak limit merely from convergence of finite variances. Here the stronger exact pointwise zero law should establish the limiting law directly, or an equally rigorous bridge must be supplied.
4. A theorem about finite quadratic traces and a separate arithmetic inequality is insufficient if the Lean conclusion never addresses the asserted limiting random variable, law, or variance. The report cannot supply all of that semantic bridge while advertising a fully formal disproof.
5. Defining a `Conjecture` predicate directly as `0 = 8/9`, or defining the target covariance to be zero, would bake in the hard part unless the predicate is rigorously connected to the exact graph/trace/expectation/limit statement.
6. Degree, graph size, graph regularity, adjacency matrix entries, centered expectation, polynomial x² evaluation, trace normalization, probability law, admissible size sequence, and limit concept all need compatible meanings. Empty finite types, nonexistent odd-size cubic ensembles, or division-by-zero conventions cannot furnish the intended counterexample.
7. Simple graphs and multigraph configuration models differ for `Tr(B²)`. The report must identify the conventional simple-graph interpretation and avoid claiming a theorem for loops/multiple edges from a simple-graph argument.
8. The source's `(d+1)` constraint language does not authorize replacing d-regular graph degree by d+1. The selected d must agree with the variance formula.
9. Asymptotic joint Gaussianity could include degenerate coordinates. The contradiction is the specifically positive x² variance, not merely the word Gaussian.
10. Any deterministic degree or n dependent normalization still leaves the centered quadratic trace zero; a claim that a standard normalization rescues the proposed positive variance would require changing the model or observable.

## Scope and authority

The current rules require complete LaTeX source and PDF, a fully compiling Lean 4 project, all auxiliary computation verified, no admissions or other incompleteness, and semantic agreement between the theorem, report, and source. The current guide also records no `sorry`, no `native_decide`, and no extra axioms. Before a solver opens a PR, existing-solution eligibility must be established by the coordinator. My task is independent review only; no submission, Git mutation, publication, or external comment is authorized here.

No candidate has yet been reviewed. This note is a source-derived evaluation standard, not an acceptance decision.
