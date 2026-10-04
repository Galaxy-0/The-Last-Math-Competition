# Solution Review — Conjecture 00000000107 (PR 463)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004122753`
**Reviewer:** independent competition review (structure, build, computation, semantics)
**Date:** 2026-10-04

## Checklist
- [x] Official bilingual conjecture read and matched byte-for-byte by `SOURCE.md`
- [x] Full LaTeX source and shipped PDF read; independent PDF builds passed
- [x] Full Lean project independently rebuilt
- [x] Direct warnings-as-errors Lean check passed
- [x] Only standard foundational axioms reported
- [x] Auxiliary Python program rerun and output independently checked
- [x] No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external hook, or kernel-check bypass
- [x] Submission adds only its own correctly named folder
- [x] Conjecture unsolved in base metadata

## Conjecture
The official claim is: for every fixed nonzero integer \(d\), as \(n\to\infty\), the Galois group of \(x^n-x-d\) over \(\mathbb Q\) is \(S_n\). Both English and Chinese versions quantify over every nonzero integer and impose no parity restriction.

## Counterexample
The submission fixes the allowed nonzero integer \(d=2\). For every even \(n\ge2\),

\[
(-1)^n-(-1)-2=1+1-2=0,
\]

so \(X+1\mid X^n-X-2\). The Galois group therefore acts faithfully on at most \(n-1\) remaining roots and has order at most \((n-1)!<n!\). Hence it cannot be isomorphic to \(S_n\). Degrees \(2(N+1)\) supply counterexamples beyond every threshold \(N\), so the failure is genuinely eventual.

## Formal audit
`lean/Main.lean` defines the actual rational polynomial \(X^d-X-C(p)\) and uses Mathlib's `Polynomial.Gal`. `FullSymmetricGalois` demands an abstract group equivalence with `Equiv.Perm (Fin d)`. The Lean proof establishes the polynomial degree, rational root, factorization, quotient degree, faithful-action bound, product-restriction bound, strict factorial inequality, arbitrarily large even counterexamples, and finally negates the nonzero-integer eventual statement.

A fresh `lake build` completed successfully. Direct `lake env lean -DwarningAsError=true Main.lean` also completed with exit 0. All printed theorems, including `conjecture107_false`, depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Independent computation
`verify.py` was rerun independently. All exact checks passed for degrees 2, 4, 6, 8, 10, and 20: evaluation at \(-1\) is zero, the displayed quotient has degree \(d-1\), multiplication by \(X+1\) reconstructs \(X^d-X-2\), and \((d-1)!<d!\). The script correctly declares these checks supplementary; the generic Galois-group argument is formalized in Lean, not inferred from finite samples.

## Documentation and build checks
The shipped PDF was read in full. Independent XeLaTeX compilation succeeded twice and produced the same two-page normalized extracted text as the shipped PDF; independent pdfLaTeX compilation also succeeded twice. Ghostscript rendered all pages successfully. The report accurately states the theorem, formalization correspondence, reused construction, and computational scope.

## Semantic conclusion
The Lean theorem non-vacuously refutes the exact eventual, all-nonzero-integer statement in the official bilingual conjecture. The parameter 2 is legitimate, even degrees are unbounded, and ruling out equality of finite group orders excludes even an abstract group isomorphism. No conjecture condition is weakened or reinterpreted.

## Verdict
APPROVED — ready for integration.
