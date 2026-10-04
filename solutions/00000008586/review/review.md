# Solution Review — Conjecture 00000008586 (PR 462)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004122738`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the source literally defines \(\Lambda_k(T)\) by existence of a \(k\)-dimensional compression of \(\lambda I-T\) with rank at most \(k-1\), and conjectures \(\Lambda_k(T)\subseteq\Lambda_{k+1}(T)\).
- Change scope: only the allowed submission directory was added; base metadata marked the conjecture unsolved and no prior solution existed.
- LaTeX: rebuilt from a fresh copy with `latexmk -pdf -interaction=nonstopmode -halt-on-error` (exit 0; two pages; no errors or unresolved warnings). Shipped and fresh text agree up to font/spacing/subscript extraction artifacts; both shipped pages were split and rasterized.
- Lean build: Lean 4.19.0 / Lake 5.0.0, Mathlib exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`; exact official dependencies linked with the supplied script and Main compiled independently. `lake build` exit 0 (`[2097/2098] Built Main`); direct warning-as-error Lean check exit 0. All nine audited theorems use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; broad hits are prose-only.
- Auxiliary program: `python3 -X utf8 verify.py` exit 0, JSON-equal to shipped evidence. I separately expanded the symbolic identity \(\det(Q^*BQ)=\det(Q^*Q)\det B\) for eight independent entries using SymPy and confirmed it exactly.
## Semantic audit
The submission first formalizes the source's literal definition: an orthonormal \(n\times k\) frame \(Q\) and the compression \(Q^*(\lambda I-T)Q\). The proof that \(Q^*Q=I\) induces an actual Euclidean isometry rules out a merely formal matrix condition.

For \(T=\operatorname{diag}(0,1)\), the normalized vector \(q=(1,1)/\sqrt2\) gives \(q^*q=1\), \(q^*Tq=1/2\), and \(q^*((1/2)I-T)q=0\). Thus \(1/2\) lies in the source-defined first range (and in the usual scalar-compression first range).

At \(k=2\), every \(2\times2\) frame with \(Q^*Q=I\) has \(\det(Q^*Q)=1\). Since \(B=(1/2)I-T=\operatorname{diag}(1/2,-1/2)\) has determinant \(-1/4\), multiplicativity gives \(\det(Q^*BQ)=-1/4\) for every admissible frame. Hence the compression is invertible and has rank exactly 2, not at most 1. Therefore \(1/2\notin\Lambda^{src}_2(T)\), disproving \(\Lambda_1(T)\subseteq\Lambda_2(T)\).

The conventional scalar definition \(Q^*TQ=\lambda I_k\) is kept separate. It always implies the source-defined rank condition because the compression is zero. The same membership at \(k=1\) and exclusion from the larger source-defined set at \(k=2\) also refutes the asserted inclusion under the standard convention. The witness is a genuine Hermitian \(2\times2\) matrix with permitted \(n=2,k=1,k+1=2\), so it is non-vacuous and defeats the unconditional inclusion clause. Other compactness, generic-nonemptiness, and envelope clauses are honestly left out of scope.
## Issues found
none blocking
## Verdict rationale
The source's rank-of-compression definition and its stated inclusion direction are faithfully encoded, and a simple Hermitian matrix gives \(1/2\in\Lambda_1\) but \(1/2\notin\Lambda_2\). The determinant argument covers every second-order compression. All formal, textual, computational, and build checks pass.

## Disposition
APPROVED — ready to merge (PR 462). Independent fresh rebuild, direct warning-as-error Lean check, axiom audit, exact auxiliary computations, PDF rebuild/comparison, source inspection, forbidden-pattern scan, and semantic audit all passed.
