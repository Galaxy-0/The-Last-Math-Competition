# Solution Review — Conjecture 00000000095 (PR 459)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004122011`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — for every fixed prime \(p\), eventually in \(d\), \(x^d-x-p\) is claimed to have Galois group \(S_d\) over \(\mathbb Q\).
- Change scope: only the allowed submission directory was added; base metadata marked it unsolved and there was no prior solution.
- LaTeX: independently rebuilt with `latexmk -pdf -interaction=nonstopmode -halt-on-error` (exit 0; two pages; no errors or unresolved warnings). Shipped and rebuilt text is exactly equal after Unicode/font normalization and whitespace removal; both shipped pages were split and rasterized.
- Lean build: Lean 4.19.0 / Lake 5.0.0, Mathlib exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Exact official dependency artifacts were linked with the provided preseed script, then Main compiled independently. `lake build` exit 0 (`[1698/1699] Built Main`); direct warning-as-error Lean check exit 0. All eight audited theorems depend only on `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; the only broad hit is prose.
- Auxiliary program: `python3 -X utf8 verify.py` exit 0 and JSON-equal to shipped evidence. I also independently checked exact divisibility by \(X+1\), quotient degree, expansion, and \(-1\)-evaluation for degrees \(2,4,6,8,10,20,42\).
## Semantic audit
For the explicitly allowed fixed prime \(p=2\) and every even \(d\ge2\), \(f_d(-1)=(-1)^d+1-2=0\). Thus \(f_d=(X+1)q_d\) with \(\deg q_d=d-1\). A splitting field of \(q_d\) already contains \(-1\), hence also splits \(f_d\); the Galois groups have equal order. More formally, Lean uses Mathlib's injective product restriction map and the trivial Galois group of a rational linear factor to get \(|Gal(f_d)|\le|Gal(q_d)|\).

For any polynomial \(q\), automorphisms of its splitting field act faithfully on the set of distinct roots, whose cardinality is at most \(\deg q\). Lean proves this through the actual Mathlib `Polynomial.Gal` root action, yielding \(|Gal(f_d)|\le(d-1)!\). Since \(d!\) is strictly larger for \(d\ge2\), no group isomorphism with \(S_d\) can exist. Lean rules out an actual multiplicative equivalence with `Equiv.Perm (Fin d)`; cardinality equality under any abstract isomorphism makes this stronger than checking only a natural labeling.

For every threshold \(N\), \(d=2(N+1)\) is even, at least \(N\), and fails. `EventualFullSymmetricForEveryPrime` correctly formalizes the usual \(\forall p\exists D\forall d\ge D\) reading, and `conjecture95_false` instantiates it at prime 2. The witness family is unbounded and non-vacuous. The prose density-one consequence is correct and not mislabeled as formalized; odd degrees and odd-prime variants are not claimed.
## Issues found
none blocking
## Verdict rationale
The even-degree family has a rational root and hence a Galois group of order strictly below \(d!\), decisively contradicting the conjecture at fixed prime 2. The Lean formalization uses genuine polynomial Galois groups and proves the required cardinality and unbounded-family assertions. All required builds and checks pass.

## Disposition
APPROVED — ready to merge (PR 459). Independent fresh rebuild, direct warning-as-error Lean check, axiom audit, exact auxiliary computations, PDF rebuild/comparison, source inspection, forbidden-pattern scan, and semantic audit all passed.
