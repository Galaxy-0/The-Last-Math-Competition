# Solution Review — Conjecture 00000000040 (PR 457)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004121044`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — for every finite \(A\subset\mathbb R\), \( |(A+A)\cap(A\cdot A)|\le |A|^{1+o(1)} \) in the supremum sense.
- Change scope: only the allowed submission directory was added; base metadata had neither `proven` nor `disproven` set and there was no prior solution.
- LaTeX: independently rebuilt with `latexmk -pdf -interaction=nonstopmode -halt-on-error` (exit 0; two pages; no errors or unresolved warnings). Shipped and rebuilt text is identical after Unicode/font normalization and whitespace removal. Both shipped pages were split and rasterized successfully.
- Lean build: Lean 4.19.0 / Lake 5.0.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; exact-revision official package artifacts preseeded, Main compiled independently. `lake build` exit 0 (`[1802/1803] Built Main`) and `lake env lean -DwarningAsError=true Main.lean` exit 0. All nine audited theorems use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; broad hits are prose-only.
- Auxiliary program: `python3 -X utf8 verify.py` exit 0 and JSON-semantically identical to the shipped output. Exact sample data for \(n=1,2,3,5,10,25\) passed. I separately recomputed actual sumsets/product sets and the embedded \(n^2\)-element grids for \(n=2,3,5,10,25\); all memberships and distinctness checks passed (at \(n=25\), \(|A|=99\), \(|I|=1299\), including the 625-element grid).
## Semantic audit
For \(A_n=\{2^i:0\le i<2n\}\cup\{1+2^i:0\le i<2n\}\), Lean uses the actual real Finsets \(A_n\times A_n\), addition/multiplication images, and their intersection. The powers have exactly \(2n\) elements, so \(2n\le|A_n|\le4n\); the upper bound uses the union inequality and therefore does not assume disjointness.

For \(0\le i,j<n\), \(s_{ij}=2^i+2^{n+j}\). It is in the sumset from two power members. Since \(1\le n+j-i<2n\), \(1+2^{n+j-i}\) is also in \(A_n\), and \(2^i(1+2^{n+j-i})=s_{ij}\), so it is in the product set. Distinctness is proved by separating columns: for \(j<l\), \(i<n\), \(2^{n+j}<s_{ij}<2^{n+j+1}\le2^{n+l}<s_{kl}\). Within a column, cancellation gives \(2^i=2^k\), hence \(i=k\). Thus \(n^2\) distinct values lie in the overlap and \(|I|\ge n^2\).

With \(n=N+64C+1\), \(M=|A_n|\le4n\), and \(I\ge n^2\), Lean proves \(CM^3\le64Cn^3<n^4\le I^2\) while \(M\ge2n\ge N\). This is uniform in every \(C,N\), so even \(I=O(M^{3/2})\) fails. `SupremumNearLinearBound` gives the standard uniform meaning of the source's \(1+o(1)\) assertion: for every \(\varepsilon>0\), all sufficiently large finite real sets satisfy \(I\le M^{1+\varepsilon}\). Taking \(\varepsilon=1/2\) and the real-power identity \((x^{3/2})^2=x^3\) for \(x\ge0\) yields the contradiction. The family is infinite, consists of positive integers embedded in \(\mathbb R\), and no hidden sign/integrality hypothesis is used.
## Issues found
none blocking
## Verdict rationale
The construction genuinely produces \(\Omega(|A|^2)\) overlap values on sets of size \(\Theta(n)\), refuting every eventual \(|A|^{1+\varepsilon}\) bound. The formal theorem quantifies over all family sizes and directly negates the uniform asymptotic interpretation. Builds, exact computations, axiom checks, and report correspondence all pass.

## Disposition
APPROVED — ready to merge (PR 457). Independent fresh rebuild, direct warning-as-error Lean check, axiom audit, exact auxiliary computations, PDF rebuild/comparison, source inspection, forbidden-pattern scan, and semantic audit all passed.
