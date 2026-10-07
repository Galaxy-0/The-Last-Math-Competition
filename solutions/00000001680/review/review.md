# Solution Review — Conjecture 00000001680 (PR 732)

**Submission:** Jackmeson1 — `solutions/00000001680/Jackmeson1_submission_20261005173059`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (bilingual, `conjectures/00000001680.md`): treewidth of random geometric graphs (unit disk, radius at the connectivity threshold) is Θ(√(log n / log log n)). Shipped `conjecture.md` is **byte-identical** to the official file.
- **LaTeX rebuild**: `latexmk -pdf` in a scratch dir succeeds (3 pages, same as shipped). pypdf comparison: normalized text ~97% sequence identity; residual diffs are extraction-order and interword-space artifacts of the shipped PDF's text layer, plus glyph-map quirks. Content matches. Cosmetic only.
- **lake build**: fresh build succeeds with **zero errors and zero warnings** (8708 jobs, Lean v4.33.1, Mathlib v4.33.1 rev 0df444a360 from poolM05), reproducing `verification/build.txt`.
- **Axioms**: `lake env lean Axioms.lean` run fresh: `C1680.treewidth_not_upper_bound` and `C1680.prob_upper_bound_eq_zero` depend only on `[propext, Classical.choice, Quot.sound]`, matching `verification/axioms.txt`. Cheat-grep clean (only benign doc mentions).
- **Aux code**: verification files' claims (build success, axiom output) reproduced exactly; no external scripts shipped.
- **Metadata**: `metadata.csv` lists 00000001680 as unsolved; no solution folder for this ID on `main`.

## Semantic audit

The conjecture is a Θ-claim, i.e. the conjunction of an upper bound tw = O(√(log n / log log n)) and a lower bound tw = Ω(√(log n / log log n)), for random geometric graphs at the connectivity threshold. The submission refutes the upper clause — which suffices for the exact negation of the conjunction — and does so deterministically, which is strictly stronger than the usual high-probability reading: for every box [-L,L]², every c₀ > 0, every real C there is N such that for all n ≥ N, all m ≥ n/2, every placement of m points in the box, every radius r with c₀·log n ≤ n·r², and every supergraph of the unit-disk graph, tw > C·√(log n / log log n). Since the connectivity threshold (π n r² ≈ log n, or asymptotic to log n) satisfies the radius hypothesis for large n, the counterexample class contains the conjectured regime; since the failure is pointwise, the "with high probability", "almost surely", and "expectation" readings of the conjecture all fail, and a corollary (`prob_upper_bound_eq_zero`) makes this formal: the bad event has measure zero under any placement measure carried by the box.

Mathlib has no treewidth, so the submission builds the theory faithfully: tree decompositions with the standard three axioms (vertex coverage, edge coverage, connected occurrence sets), width = max bag size − 1, treewidth = minimum width (attained, via the one-bag decomposition), and from scratch the Helly property of subtrees of a tree (three-set case plus induction), yielding clique-in-a-bag and ω(G) ≤ tw(G) + 1 — all standard and correctly formalized. The decisive mechanism is a genuine argument about the actual geometric model, not a toy: tile the box with squares of side r/2; there are at most (M+1)² ≤ 32L²/r² + 2 of them (M = ⌊2L/(r/2)⌋ ≤ 4L/r, and the slack inequality reduces to (4L/r − 1)² ≥ 0 — I verified this by hand); by pigeonhole some cell holds at least m/(32L²/r² + 2) points; two points in a cell are less than √2·(r/2) < r apart, so the cell is a clique of size Ω(m r²/L²); the radius hypothesis c₀ log n ≤ n r² with n ≤ 2m makes this Ω(log n); and Helly forces tw ≥ |K| − 1 = Ω(log n), which eventually dominates C·√(log n / log log n) for every fixed C (the final algebra, ℓ = log n ≥ max(X², e), x = √ℓ, |C|x < ℓ/A − 1 ≤ tw with A = 64L²/c₀ + 4, checks out symbolically). The theorem's generality — arbitrary supergraphs — also covers the toroidal metric (torus distance ≤ Euclidean distance), disclosed in the tex; the m ≥ n/2 point-model covers binomial and Poisson samplings; and the literature remark (Mitsche–Perarnau, STACS 2012, Θ(log n/log log n) for constant radius) is consistent with, and weaker than at threshold, what is proved. The claim that the conjectured √(log n/log log n) scale is false is genuinely true mathematics.

## Issues found

- `verification/SHA256SUMS.txt` is stale: entries for `conjecture.md` and `lean/Conjecture1680/Basic.lean` are pre-final-commit hashes. Non-blocking: `conjecture.md` is byte-identical to the official file, and the build/axiom claims were re-verified fresh on the shipped source.
- The connectivity threshold itself is not formalized (it is an informal regime); the theorem instead covers every radius with n r² ≥ c₀ log n, a superset — disclosed and stronger, so no faithfulness gap.
- The lower-bound clause of the Θ is not addressed (nor needs to be, since the upper clause fails); the submission says so explicitly.

## Verdict

APPROVED. The submission formalizes treewidth and the unit-disk graph from first principles with correct standard definitions, proves the exact negation of the upper clause of the Θ-claim deterministically (hence under every probabilistic reading), and the argument — grid pigeonhole, clique, Helly — is a faithful and verifiable analysis of the conjecture's own model at its own threshold scale. Build, axioms, source fidelity and PDF checks all pass; the only finding is the stale checksum file.
