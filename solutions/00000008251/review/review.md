# Solution Review — Conjecture 00000008251 (PR 435)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004061156`  
**Reviewer:** independent competition reviewer  
**Date:** 2026-10-04

## Checklist results

- **Conjecture correspondence.** Attacked the official finite-state extremal-count conjunct: martingale-measure extreme points should equal `|Ω| − rank(assets)`. A concrete finite market proves one extreme point versus zero.
- **Repository structure.** PR head `357084c1...`, from clean base `4cc82278...`, adds only its correctly named submission folder. Base metadata has no prior solve. No forbidden root/metadata/conjecture edits.
- **LaTeX/PDF.** Read the full report and shipped two-page PDF. Independely ran `pdflatex` twice, both exit 0. Ghostscript rendered the shipped PDF successfully; fresh and shipped content match.
- **Lean.** Independently linked the official shared Mathlib, ran `lake build` (exit 0, 2804 targets), and replayed `Main.lean` with `-DwarningAsError=true` (exit 0). All seven audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- **Forbidden content.** No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, `implemented_by`, or kernel-check bypass.
- **Auxiliary code.** None needed; all relevant finite probability, rank, and convex-extreme calculations are formal Lean objects.

## Semantic audit

For `Ω={0,1}`, take Arrow securities with payoff matrix `I₂` and initial prices `(1/2,1/2)`. Portfolio `h` pays `(h₀,h₁)` and costs `(h₀+h₁)/2`, so the market is complete, `(1,1)` supplies a constant numeraire, and there is no arbitrage. The martingale equations force `Q{0}=Q{1}=1/2`; finite measures are determined by these masses, so both the ordinary and equivalent martingale-measure sets equal the singleton uniform measure. A singleton convex set has one extreme point, while the conjectured formula gives `2−2=0`.

Lean proves payoff identity/rank, completeness, numeraire replication, no-arbitrage, actual integral equations, measure uniqueness, both absolute-continuity directions, singleton feasible sets, and the Mathlib extreme-point count. The counterexample is non-vacuous and directly falsifies a universal conjunct of the official statement.

## Issues found

None blocking.

## Verdict rationale

The complete two-state Arrow-security market is a legitimate finite-state arbitrage-free market whose martingale set has one extreme point, contradicting the asserted zero. Independent PDF, Lean, axiom, structure, and semantic checks pass.

## Disposition

**APPROVED**
