# Solution Review — Conjecture 00000001196 (PR 484)

**Submission:** jilint777 — `jilint777_submission_20261004143853`
**Reviewer:** independent competition reviewer (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the official statement claims `M((k),(k))=2^{k−1}` in addition to its coefficient bound.
- Path policy: pass — only the submitter's own folder was added; base metadata is unsolved/undisproved.
- LaTeX: independent `latexmk -pdf` build exited 0; all 5 pages extracted/rendered and read. Content agrees with the shipped PDF.
- Lean: core-only Lean 4.19 project built independently with `lake build`; exit 0. Direct warning-as-errors Lean check exited 0.
- Axioms: finite computational identities use no axioms; general negation/uniqueness proofs use only `[propext, Quot.sound]`.
- Forbidden content: no `sorry`, `admit`, `native_decide`, extra axiom, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`.
- Auxiliary code: `python3 verify.py` exited 0. I audited its independent marked-shifted-tableau construction and exact rational solver; all expected k=1..5 readings and the k=3 expansion reproduced.

## Semantic audit
The report proves `Q_(k)Q_(k)=2Σ_{j=0}^{k−1}Q_(2k−j,j)` from the defining `q_r` generating relation, and derives the corresponding P-basis expansion. Thus the largest standard coefficient is 2 for every k≥2, not `2^{k−1}` once k≥3. At k=3: `Q₃Q₃=2Q₆+2Q₅₁+2Q₄₂` and `P₃P₃=P₆+2P₅₁+2P₄₂`, so `M((3),(3))=2≠4`.

Lean computes this decisive instance from scratch in `ℤ[x₁,x₂,x₃]` using the generating function and Schur Pfaffian. Since all strict partitions of 6 have at most three parts and specialization is a ring homomorphism, the explicit triangular coefficient table proves uniqueness of the full-ring expansion coefficients. Lean proves existence, uniqueness, all eight P/Q normalization readings, and the final incompatibility of the value and bound clauses. Non-vacuity checks show both predicates can hold in suitable cases. The Python script independently verifies the same identities from marked shifted tableaux.

## Issues found
- The all-k identity and full-ring existence are paper-only, clearly disclosed. This is not blocking: Lean formalizes the unique decisive k=3 case, and I checked the general algebraic proof line by line.
- No separate byte-identical bilingual source file is shipped, but the report quotes the English claim exactly and accurately describes the Chinese version; I compared directly with the official conjecture.

## Disposition
APPROVED — fresh LaTeX, Lean, and Python builds pass; only standard/no axioms occur; and the unique k=3 expansion decisively gives `M((3),(3))=2` rather than 4 under both standard readings (with every mixed normalization also handled).
