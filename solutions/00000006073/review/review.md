# Solution Review — Conjecture 00000006073 (PR 525)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004170844`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — spurious minima are defined as stationary, nonminimum points; the final conjunct asserts their attraction basins have measure zero, strictly in the analytic case.
- Change scope: only the allowed submission directory was added. Base metadata marks the conjecture unsolved and no prior solution existed.
- LaTeX: independently rebuilt with `latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex` (exit 0; two pages; no warnings or errors). Shipped/fresh text agrees up to font/spacing extraction artifacts; both shipped pages were split and rasterized.
- Lean build: Lean 4.19.0 / Lake 5.0.0, Mathlib exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`; exact official dependencies linked via the supplied script and Main compiled independently. `lake build` exit 0 (`[2224/2225] Built Main`); direct warning-as-error Lean check exit 0. All ten audited theorems use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; broad hits are prose-only.
- Auxiliary code: none is supplied or needed.
## Semantic audit
The objective \(f(x)=x^3\) is a polynomial and Lean proves analyticity at every real point. Its derivative/gradient is \(3x^2\), hence the origin is stationary. It is not a local minimum because every ball around 0 contains \(-\varepsilon/2\), where \(f<0=f(0)\). Therefore 0 satisfies the source's explicit stationary-nonminimum definition; no nondegeneracy or strict-saddle hypothesis appears in the official statement.

For any \(s>0\), \(u_s(t)=s/(1+3st)\) is global for \(t\ge0\), equals \(s\) initially, and has derivative \(-3s^2/(1+3st)^2=-3u_s(t)^2=-\nabla f(u_s(t))\). Lean proves genuine `HasDerivAt` at every nonnegative time, not a formal scalar assignment. Since \(u_s(t)\to0\), every positive start belongs to the defined forward gradient-flow basin. In particular \((0,1)\subseteq B\). Lebesgue measure monotonicity and the interval formula give \(\lambda(B)\ge1\), so the basin is not null. Because `volume` is used directly and measure monotonicity applies, no separate measurability assumption is needed.

The report correctly limits the disproof to the basin-nullity clause and continuous gradient flow. It does not dispute known results for nondegenerate strict saddles or address the separate smoothing/Morse-index clauses.
## Issues found
none blocking
## Verdict rationale
A real analytic stationary nonminimum has a basin of positive Lebesgue measure under the standard continuous gradient flow, directly contradicting the conjecture's analytic nullity clause. The flow, derivative, limit, basin, and measure arguments are all formalized and rebuild cleanly.

## Disposition
APPROVED — ready to merge (PR 525). Independent fresh rebuild, direct warning-as-error Lean check, axiom audit, PDF rebuild/comparison, source inspection, forbidden-pattern scan, and semantic audit all passed.
