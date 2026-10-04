# Solution Review — Conjecture 00000000438 (PR 502)

**Submission:** jilint777 — `jilint777_submission_20261004150531`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and scope.** Relative to clean base `4cc82278`, the three-dot diff adds only the correctly named personal submission folder. Base metadata marks 00000000438 unsolved, and an exact-ID PR search finds only this PR. The report quotes the English official statement and its Chinese counterpart accurately; I independently compared the claim with both official languages.
- **LaTeX and PDF.** I read the complete five-page report, every source/config/verification file, all 395 Lean source lines, and all 245 Python lines. A fresh `latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex` succeeded (exit 0; 5 pages). Text extraction and normalized comparison show the shipped and fresh PDFs agree (similarity 0.99924), and all five fresh pages were rendered with Ghostscript.
- **Lean.** This is a self-contained Lean 4.19.0 project with no packages. In a fresh copied directory, `lake build` completed successfully. Direct `lake env lean -DwarningAsError=true Main.lean` exited 0. Central audits report only `[propext, Classical.choice, Quot.sound]`; the two purely finite Eulerian-counting theorems depend on no axioms.
- **Auxiliary program.** I independently ran `python3 verify.py`; it exited 0 and printed `ALL CHECKS PASSED`. It computes primitive dimensions by exact rational coproduct kernels (`n≤8`), modulo `2^61−1` (`n≤10`), QSym quasi-shuffle duality (`n≤7`), and the PBW/Hilbert-series identity (`n≤10`). It also computes Eulerian numbers by both closed formulas and brute force over permutations through `n=9`.
- **Forbidden-content scan.** No `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `skipKernelTC`, or kernel-trust override occurs. Lean uses kernel-checked `decide`/`decide +kernel`, not native evaluation.

## Semantic audit

The official object is the Hopf algebra of **noncommutative** symmetric functions, NSym: the free associative algebra on generators `S_1,S_2,…` with algebra coproduct

`Δ S_k = Σ_{i+j=k} S_i⊗S_j` (`S_0=1`).

The primitive space in degree `n` is the kernel of the reduced coproduct `Δ̄x=Δx−x⊗1−1⊗x`. This is the only reading with the officially stated “n-th homogeneous dimension … verifiable for n≤10”; the report also explains why commutative Sym, QSym, infinitesimal characters, and indecomposables are not the named object.

In degree 3, use the basis `S_3, S_{21}, S_{12}, S_{111}`. Direct expansion gives:

- `Δ̄S_3 = S_2⊗S_1+S_1⊗S_2`;
- `Δ̄S_{21}=Δ̄S_{12}=S_2⊗S_1+S_1⊗S_2+S_{11}⊗S_1+S_1⊗S_{11}`;
- `Δ̄S_{111}=3S_{11}⊗S_1+3S_1⊗S_{11}`.

Therefore

`Δ̄(aS_3+bS_{21}+cS_{12}+dS_{111}) = (a+b+c)(S_2⊗S_1+S_1⊗S_2)+(b+c+3d)(S_{11}⊗S_1+S_1⊗S_{11})`.

The tensor basis is independent, so primitivity is exactly `a+b+c=0` and `b+c+3d=0`. These two independent equations in four coordinates give dimension `2`. Explicit independent witnesses are `Ψ_3=3S_3−S_{21}−2S_{12}+S_{111}` and `[S_2,S_1]=S_{21}−S_{12}`. Lean proves the full iff criterion, both witnesses, independence, and an explicit dependence among any three primitives; it also proves uniqueness of dimension `m=2`. Integer coefficient vectors suffice for rational dimension by clearing denominators, a bridge proved in the report.

Under the standard zero-based descent/ascent convention, `A(3,1)` counts the four permutations `132,213,231,312` with one descent; under the one-based OEIS convention it is `1`. Neither is `2`. More generally, one-descent Eulerian values are `2^m−m−1`, while one-based values are `1`; neither sequence ever takes value `2`, so even an index shift cannot rescue the formula. Lean checks all four convention variants and negates the dimension clause.

The auxiliary computations independently return primitive dimensions

`1,1,2,3,6,9,18,30,56,99` for `n=1..10`

and Eulerian values `2^n−n−1` or all `1`. Thus the discrepancy starts decisively at `n=3` and continues through the officially checkable range. The undefined “generalized Lie n-algebra” is not needed: any graded isomorphism preserving the stated homogeneous dimensions would transfer this false dimension formula to `Prim(NSym)`.

The formal model is non-vacuous: compositions enumerate the actual NSym degree basis, tensors represent the actual tensor-square basis, the coproduct is extended multiplicatively from its definition, and `PrimDim` is genuine linear dimension rather than a bare numeral certificate.

## Verdict rationale

The mathematics and formalization agree, the decisive degree-3 computation is kernel-checked and independently reproduced three ways, Eulerian conventions are handled robustly, and the report carefully addresses alternative readings. Builds, strict replay, auxiliary computation, PDF verification, scans, and duplicate checks all pass.

## Disposition

APPROVED — ready for merge (PR 502). No merge action was taken by this reviewer.
