# Solution Review — Conjecture 00000000585 (PR 634)

**Submission:** Galaxy-0 — `solutions/00000000585/Galaxy-0_submission_20261005131900`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (`conjectures/00000000585.md`, bilingual). Formalizable content: for every prime power q, T_G(q+1, q−1) > 0 and yields an effective count. The introductory descriptor mentions log-concavity but states no sequence or inequality to formalize.
- **LaTeX rebuild:** pass — `build_pdf.sh` succeeds; 3 pages, no errors.
- **PDF comparison:** pass — rebuilt `solution.pdf` text identical to shipped (7233 chars both, all 3 pages).
- **Lean build:** pass — `lake build` zero errors on pinned Lean 4.31.0 (core only); both `Tutte585.lean` and `Examples.lean` compile; `#eval` prints 13 as claimed.
- **Axioms:** pass — `conjecture_00000000585` depends only on `propext`, `Classical.choice`, `Quot.sound` (the allowed set); no `sorry`, `native_decide`, custom axioms, `unsafe`, or `extern`; Classical reasoning is confined to the correctness proof of the cut test.
- **Auxiliary code:** pass — `check_model.py` independently rerun: "PASS: 753 graph/parameter cases" (matches `VALIDATION.txt`); it checks the cut-rank against union-find rank, the rank bounds, the positive lower bound q^r(E), and exact duplicate-free object counts for small graphs, at q = 2, 3, 4. `SHA256SUMS` verifies on a pristine extraction. Kernel-checked example values match the true Tutte polynomial: loop T=y → 1 at (3,1) and 2 at (4,2); bridge T=x → 3; parallel pair T=x+y → 4; triangle T=x²+x+y → 13 at (3,1), and `countedObjects triangle 2` has length 13.
- **Semantic audit:** pass — see below.
- **Source statement ground truth:** pass; the report quotes the official text and pins the exact upstream revision.

## Semantic audit

The decisive theorem `conjecture_00000000585` states, for **all** finite multigraphs G (loops, parallel edges, disconnected, empty allowed) and **all** natural q ≥ 2:

0 < tutte G (q+1) (q−1)  ∧  (countedObjects G q).length = tutte G (q+1) (q−1)  ∧  (countedObjects G q).Nodup.

This is the conjecture in a strictly stronger form: the quantifier over q ≥ 2 strictly contains all prime powers; the "effective count" is realized as an explicit, executable, duplicate-free enumeration whose cardinality is exactly the evaluation; and the proof yields the stronger bound T_G(q+1,q−1) ≥ q^{r(E)} > 0.

Faithfulness of the object: `tutte` is the standard rank-subset expansion Σ_A (x−1)^{r(E)−r(A)} (y−1)^{|A|−r(A)} with r = |V| − c(A), c counting all components including isolated vertices; `componentCount` counts least vertices per component, which is correct because each nonempty component has a unique least vertex. Natural-number subtraction in the exponents equals true subtraction here because r(A) ≤ r(E) and r(A) ≤ |A| hold for graphic matroids; these two facts are proved in the written report (§1) rather than in Lean, a disclosed scope decision that does not weaken the theorem (truncated subtraction only makes the stated Lean claims harder, not easier — the Lean theorems hold of the defined function unconditionally, and the defined function provably equals the true polynomial value at the specializations used). The mathematics itself is sound: every summand is nonnegative at x = q+1, y = q−1 with q ≥ 2, and the empty-subset summand q^{r(E)} is strictly positive; I verified the expansion and all example values by hand. The submission makes no claim about the unformalizable log-concavity descriptor and says so explicitly.

## Issues found

- None material. Observation: the rank bounds r(A) ≤ r(E), r(A) ≤ |A| are paper-only (not separate Lean lemmas); this is disclosed in README/VALIDATION/report and does not affect the truth or faithful interpretation of the proven statements.

## Verdict

**APPROVED** — a complete, honest, machine-checked proof of the positivity and effective-count assertions of conjecture 00000000585, in a form strictly stronger than requested.
