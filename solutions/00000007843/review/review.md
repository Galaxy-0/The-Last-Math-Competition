# Solution Review — Conjecture 00000007843 (PR 571)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004205100`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture `conjectures/00000007843.md` read in full: on d-regular graphs the random greedy independent-set size is "always" sandwiched at n·log d/(d + log d) up to a 1+o(1) factor; and the upper/lower gap is controlled by the depth of local tree-like neighborhoods. The submission's `verification/original.md` is **byte-identical** to the official file (diff clean).
- LaTeX: `proof.tex` rebuilt from scratch with `latexmk -pdf` (clean, 2 pages). MuPDF text comparison of shipped vs rebuilt PDF: identical content — the single difference is one ﬀ ligature codepoint.
- Lean: fresh `lake build`, lean4 v4.19.0, Mathlib pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b` — **0 errors, 0 warnings**.
- Axioms: `Main.lean` prints audits for all seven results (`degree_regular`, `actual_output`, `expectation_one`, `almost_sure_one`, `benchmark_diverges`, `relative_limit_zero`, `claimed_relative_asymptotic_fails`); every one depends only on `[propext, Classical.choice, Quot.sound]`. No `sorry`/`native_decide`/`axiom`/`unsafe`/`admit` anywhere in the submission.
- Auxiliary code: none beyond verification logs (`verification/validation.txt`, empty `direct-pr-search.json`, build/pdf logs — consistent with the artifacts).
- Repo metadata: conjecture unsolved; submission claims a disproof.

## Semantic audit
The conjecture's first clause is a universal two-sided asymptotic sandwich: greedy size = (1±o(1))·B(n,d) on d-regular graphs, with no triangle-free, girth, or local tree-likeness restriction stated. The submission's counterexample is the complete graph K_{d+1}, for every d ≥ 2 — genuinely d-regular (Lean: `IsRegularOfDegree d` for the top graph on `Fin (d+1)`), with n = d+1. The random greedy process is formalized as the actual fold over the vertex permutation, adding a vertex exactly when it is unchosen and non-adjacent to all chosen vertices — the standard process of the definition clause. On a complete graph the first permutation element is added and every later element is adjacent to it, so the output is exactly the singleton {p 0} for **every** permutation (proved, not assumed); the failure is deterministic across all orders, and under the genuine uniform PMF on the full permutation group the size is almost surely 1 with Bochner expectation exactly 1.

The benchmark is B(d+1,d) = (d+1)·log d/(d + log d). Since 0 ≤ log d ≤ d for d ≥ 2, B ≥ (d·log d)/(2d) = (log d)/2 → ∞ (Lean: `benchmark_diverges`), so the relative expected size 1/B → 0 (`relative_limit_zero`), which cannot tend to 1 (`claimed_relative_asymptotic_fails`) — refuting the lower half of the sandwich and hence the 1+o(1) clause. I re-verified numerically (B = 0.77, 1.07, 2.06, 4.45 at d = 2, 3, 10, 100; ratio 1/B = 0.93, 0.49, 0.23 → 0). Notably the refutation is robust to the English formula's parsing ambiguity: the alternative reading (n log d)/d + log d also diverges (4.8, 9.3, 27.6 at d = 10, 100, 10⁶), so the ratio still tends to 0 under either parse. The asymptotic regime n = d+1 → ∞ is legitimate for a 1+o(1) law whose benchmark involves log d, and the submission states the regime explicitly. The official text's second clause (gap controlled by tree-neighborhood depth) is an additional assertion after a semicolon — it does not qualify the first clause's "always" — and in any case the conjecture is a conjunction, so refuting the first clause suffices; the report says exactly this and does not dispute locally-tree-like restricted theorems.

Faithfulness details: the greedy step uses the graph's actual adjacency relation; the vertex order is a genuine permutation (`Equiv.Perm` mapped over `finRange`, with a `Perm` certificate); the probability law is the normalized uniform PMF on the whole permutation group with proved probability-measure instance; expectation is the true Bochner integral; the final theorem is the plain negation of `Tendsto relativeSize atTop (𝓝 1)`. Quantifier structure matches: one d-regular family, deterministic-in-the-order size 1, benchmark → ∞, relative size → 0 ≠ 1.

## Issues found
None blocking. (One ff-ligature extraction difference between Tectonic and pdflatex outputs.)

## Verdict
APPROVED. The complete-graph family is a mathematically correct, a.s.-deterministic counterexample to the conjecture's unrestricted universal sandwich clause, formalized end-to-end with genuine graphs, permutations, greedy dynamics, probability law and limits; the build is clean with zero warnings, only the three standard axioms are used, and all document, source-identity and numeric checks pass.
