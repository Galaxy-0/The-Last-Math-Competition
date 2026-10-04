# Solution Review — Conjecture 00000003961 (PR 460)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004122224`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — for every \(k\le n/2\), the lazy walk on \(J(n,k)\) is claimed to exhibit total-variation cutoff with a stated cutoff-time formula.
- Change scope: only the allowed submission directory was added; base metadata marked the conjecture unsolved and no prior solution existed.
- LaTeX: rebuilt from a fresh copy with `latexmk -pdf -interaction=nonstopmode -halt-on-error` (exit 0; two pages; no errors or unresolved warnings). Shipped and fresh text is exactly equal after Unicode/font normalization and whitespace removal. Both shipped pages were split and rasterized.
- Lean build: Lean 4.19.0 / Lake 5.0.0, Mathlib exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`; official exact-revision dependency artifacts linked with the supplied script and Main compiled independently. `lake build` exit 0 (`[1629/1630] Built Main`); direct warning-as-error check exit 0. Printed dependencies are only the permitted standard axioms (one elementary theorem uses just `propext`/`Quot.sound`; the others add `Classical.choice`).
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; broad hits are prose-only.
- Auxiliary program: `python3 -X utf8 verify.py` exit 0, JSON-equal to shipped evidence. I also independently recomputed \(d_N(t)=(N-1)N^{-1}a_N^t\) and the two mixing times for every \(N=5,\dots,30\), obtaining ratio 2 each time.
## Semantic audit
For \(k=1\), vertices are singleton subsets and distinct vertices have symmetric difference size 2, so \(J(N,1)\cong K_N\). Lean constructs actual singleton Finsets, proves the symmetric-difference adjacency rule and the bijection from labels, and derives degree \(N-1\). This family satisfies \(1\le N/2\) for every \(N\ge2\), hence lies in the conjecture's stated parameter range; the source does not impose \(k\to\infty\).

The standard half-lazy transition matrix has \(P(i,i)=1/2\) and \(P(i,j)=1/[2(N-1)]\) for \(i\ne j\). Lean matches this to the actual Johnson graph and neighbor count. With \(a=(N-2)/(2(N-1))\) and \(U\) the all-\(1/N\) idempotent matrix, \(P=aI+(1-a)U\), so \(P^t=a^tI+(1-a^t)U\). Therefore, from every starting state, total variation to uniform is exactly \((N-1)N^{-1}a^t\). The proof evaluates the diagonal and \(N-1\) off-diagonal absolute differences rather than assuming a mixing estimate.

For \(N\ge5\): \(d_N(0)>3/4\), \(1/4<d_N(1)<3/4\), and \(d_N(2)\le1/4\). Lean proves these exact comparisons and that the admissible-time sets are nonempty, yielding \(t_{\rm mix}(3/4)=1\) and \(t_{\rm mix}(1/4)=2\). The standard cutoff ratio criterion requires \(t_{\rm mix}(\varepsilon)/t_{\rm mix}(1-\varepsilon)\to1\); at \(\varepsilon=1/4\) this ratio is identically 2. `HasTotalVariationCutoff` faithfully encodes that real-limit criterion, and `no_total_variation_cutoff` refutes it. Since the universal cutoff assertion already fails, the proposed multiplier formula need not be evaluated. The report honestly limits the result to the stated conjecture and does not address a modified growing-\(k\) version.
## Issues found
none blocking
## Verdict rationale
The \(k=1\) family is admissible, exactly analyzed, and has constant mixing-time ratio 2, so it decisively contradicts total-variation cutoff for all \(k\le n/2\). Formal and textual statements correspond, all builds and exact computations pass, and no forbidden proof mechanisms occur.

## Disposition
APPROVED — ready to merge (PR 460). Independent fresh rebuild, direct warning-as-error Lean check, axiom audit, exact auxiliary computations, PDF rebuild/comparison, source inspection, forbidden-pattern scan, and semantic audit all passed.
