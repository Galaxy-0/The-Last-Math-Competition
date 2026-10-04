# Solution Review — Conjecture 00000008430 (PR 399)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004041959`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "The count of Schubert configurations (chains of subspaces determined by dimension conditions) over finite fields is a q-polynomial; the leading coefficient is 1 and its roots are integers."
- LaTeX: recompiled with pdflatex (twice) in /tmp/tlmc-review5/scratch/pr-399, exit 0, 2 pages; shipped report.pdf (42491 bytes, 2 pages) extracts to the same text as report.tex. Real matching PDF.
- Lean build: `lake build` exit 0 (1671 targets); only output = 4 info lines from `#print axioms`, all `[propext, Classical.choice, Quot.sound]`; no warnings.
- Forbidden content: grep over lean/Main.lean (only source file) for sorry/admit/native_decide/axiom decl/unsafe/implemented_by/extern/skipKernelTC: no hits. Toolchain Lean 4.19.0, mathlib pinned c44e0c8e — matches required env.
- Auxiliary code: none shipped; independent recomputation done: sympy roots of q²+q+1 are (-1±i√3)/2 (non-real, hence non-integer), monic confirmed; brute-force enumeration of lines of F_p³ for p ∈ {2,3,5,7,11} gives {7,13,31,57,133} = p²+p+1 in every case.
## Semantic audit
Literal claim: for a Schubert configuration (a chain of subspaces determined by dimension conditions), the finite-field count is a monic q-polynomial **whose roots are integers**. The submission exhibits the chain family 0 ⊊ L ⊊ F_q³ with dim L = 1 — literally "a chain determined by dimension conditions" per the conjecture's own definition — whose count over every finite field is |Gr(1,3)| = (q³−1)/(q−1) = q²+q+1, a monic polynomial with non-real roots ζ = (-1+i√3)/2. Lean encodings are faithful:
- `def Lines (k : Type*) [Field k] := { L : Submodule k (Fin 3 → k) // Module.finrank k L = 1 }` — actual one-dimensional submodules; with fixed endpoints 0 ⊂ k³ these are exactly the chains.
- `theorem count_lines (k : Type*) [Field k] [Finite k] : Nat.card (Lines k) = (Nat.card k)^2 + Nat.card k + 1` — via Mathlib's proved `Projectivization.equivSubmodule` and `Projectivization.card_of_finrank`; holds for EVERY finite field, not a spot-check.
- `theorem counting_polynomial_unique (P : Polynomial ℂ) (hP : ∀ (k : Type) [Field k] [Finite k], P.eval (Nat.card k : ℂ) = (Nat.card (Lines k) : ℂ)) : P = countPolynomial` — uses ZMod p over all primes + polynomial identity theorem, so countPolynomial X²+X+1 is provably THE counting polynomial (defeats any "wrong polynomial" objection; this is not a numeric-facts-only proof).
- `theorem countPolynomial_monic : countPolynomial.Monic` — confirms the other two clauses of the conjecture HOLD, isolating the failure to the integer-root clause.
- `theorem conjecture_00000008430 : (∀ (k : Type) [Field k] [Finite k], countPolynomial.eval (Nat.card k : ℂ) = (Nat.card (Lines k) : ℂ)) ∧ ∃ z : ℂ, countPolynomial.IsRoot z ∧ ¬ ∃ m : ℤ, z = (m : ℂ)` — with zeta = ⟨-1/2, √3/2⟩, root equation and non-integer (non-real) nature kernel-verified.
Not vacuous: the counting identity is a universally quantified equality over all finite fields, and the second conjunct positively exhibits a root and proves it is no integer cast. Hypotheses: the conjecture imposes none beyond the definition; the family satisfies the definition literally. Scope note: the full Grassmannian is the maximal Schubert variety (trivial position condition); the conjecture's text carries no restriction to proper Schubert varieties or nontrivial incidence conditions, so this is admissible under the literal bilingual statement — and the failure is robust, not knife-edge: e.g. the richer chain 0 ⊂ L₁ ⊂ L₂ ⊂ F_q⁴ (dims 0,1,2,4) has count [4 choose 2]_q = (q²+1)(q²+q+1) = q⁴+q³+2q²+q+1, likewise monic with roots ±i, (-1±i√3)/2 (sympy-verified). Flagged for coordinator awareness as an "extremal" configuration choice, but it is squarely inside the stated definition.
## Issues found
none blocking (note: example uses the maximal Schubert configuration — admissible since the text has no restriction; robustness confirmed via Gr(2,4))
## Verdict rationale
The counting fact |Gr(1,3)(F_q)| = q²+q+1 is proved in Lean for every finite field with uniqueness of the counting polynomial, monicity is confirmed, and the non-real root ζ = (-1+i√3)/2 is kernel-verified to satisfy the polynomial and to be no integer — directly contradicting the conjecture's literal "roots are integers" clause while its own definition of Schubert configuration (dimension-determined chains) is satisfied verbatim. Build is clean with only standard axioms, the shipped PDF matches the recompiled one, and independent sympy/brute-force computations confirm every number. This is a genuine, fully formal disproof of the stated conjecture.

## Disposition
APPROVED — merged into main (PR 399). Independent fresh rebuild of the Lean project (Mathlib-pinned, exit 0; only standard foundational axioms; no sorry/native_decide/extra axioms), LaTeX recompilation, auxiliary-script re-runs where shipped, independent recomputations, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
