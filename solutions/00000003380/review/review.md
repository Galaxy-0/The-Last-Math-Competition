# Solution Review — Conjecture 00000003380 (PR 461)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004122239`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the first explicit clause says all automorphisms are inner when the algebra is noncommutative; no simplicity, factor, or central-simplicity hypothesis is stated.
- Change scope: only the allowed submission directory was added; base metadata marked the conjecture unsolved and there was no prior solution.
- LaTeX: rebuilt from a fresh copy with `latexmk -pdf -interaction=nonstopmode -halt-on-error` (exit 0; two pages; no errors or unresolved warnings). Shipped/fresh differences are font-encoding artifacts for \(\times\), arrows, and ligatures; the mathematical content agrees, and both shipped pages were split and rasterized.
- Lean build: Lean 4.19.0 / Lake 5.0.0, Mathlib exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`; exact official dependencies linked with the supplied script and Main compiled independently. `lake build` exit 0 (`[1520/1521] Built Main`); direct warning-as-error Lean check exit 0. All nine audited theorems use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; broad hits are prose-only.
- Auxiliary code: none is supplied or needed. I independently recomputed the displayed \(2\times2\) products: \(PQ=\mathrm{diag}(1,0)\neq\mathrm{diag}(0,1)=QP\).
## Semantic audit
The witness is \(A=M_2(\mathbb C)\times M_2(\mathbb C)\), an actual product of Mathlib matrix algebras. It is noncommutative: the displayed nilpotent matrices \(P,Q\) satisfy \(PQ\ne QP\), so \((P,0)\) and \((Q,0)\) do not commute.

Component exchange is the Mathlib product ring equivalence with verified complex-algebra linearity, hence a genuine \(A\simeq_{\mathbb C}A\). It preserves the componentwise conjugate-transpose adjoint. The element \(e=(I,0)\) is idempotent and central. For every unit \(u\in A^\times\), \(ueu^{-1}=euu^{-1}=e\). Thus any inner automorphism, by definition implemented by such a unit, fixes \(e\). But exchange sends \(e\) to \((0,I)\ne e\). Therefore exchange is outer. Excluding all internal units also excludes every unitary implementer, so the source's more restrictive unitary wording cannot rescue the universal assertion.

The implementing unit is correctly required to lie in \(A^\times\); a larger ambient \(4\times4\) permutation matrix is irrelevant to innerness in the product algebra. `AllNoncommutativeAutomorphismsInner` quantifies over complex noncommutative algebras and all complex algebra automorphisms, exactly the necessary universal clause of the official statement. The witness instantiates this predicate non-vacuously. The unspecified “measure of innerness” need not be defined once the universal innerness assertion fails; the report says so and does not claim a general C*-algebra theorem.
## Issues found
none blocking
## Verdict rationale
A noncommutative algebra has been constructed with an explicit automorphism that must move a central idempotent, while every inner automorphism fixes it. This is a complete, non-vacuous counterexample to the stated universal assertion. Builds, axiom checks, PDF reconstruction, and source correspondence all pass.

## Disposition
APPROVED — ready to merge (PR 461). Independent fresh rebuild, direct warning-as-error Lean check, axiom audit, PDF rebuild/comparison, source inspection, forbidden-pattern scan, independent matrix check, and semantic audit all passed.
