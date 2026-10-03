# Solution Review — Conjecture 00000007292 (PR 338)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003104000`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — rank and crank of integer partitions are equidistributed, and the distribution's generating function is the Jacobi triple product; submission disproves the equidistribution clause at n=4 (a conjunction is refuted by one false conjunct).
- LaTeX: compiled ok (pdflatex twice, exit 0, zero errors); shipped main.pdf is a real 2-page PDF (41 KB) whose content matches main.tex; my recompile also 2 pages.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, "Build completed successfully", with `-DwarningAsError=true`; only output is `#print axioms` info lines (propext, Classical.choice, Quot.sound — all standard).
- Forbidden content: none — grep for sorry/admit/native_decide/axiom/unsafe/implemented_by/extern found nothing.
- Auxiliary code: verify.cjs exit 0, output identical to auxiliary-results.json recorded stdout; my independent python3 recomputation of partitions of 4 gives ranks {3,1,0,-1,-3} and cranks {4,0,2,-2,-4}, N(4,4)=0 != 1=M(4,4) — exactly the claimed mismatch (also fails at n=1,2,3; n=4 wisely avoids the n=1 crank convention).
## Semantic audit
Conjecture (EN+CN): "The equidistribution of rank and crank holds ...". Natural reading: for all m and all n, N(m,n)=M(m,n); no modulus is specified (SOURCE.md notes this, faithfully reproducing the official .md verbatim — verified by exact string diff).

Lean definitions: `IsPartition n parts := parts.Pairwise (· ≤ ·) ∧ (∀ a ∈ parts, 0 < a) ∧ parts.sum = n` — the standard partition. `rank parts := Int.ofNat (parts.headD 0) - Int.ofNat parts.length` — Dyson rank (head is largest by the proved `first_is_largest`). `crank parts := if ones parts = 0 then head else #(parts > ones) - ones` — exactly the Andrews–Garvan crank (ω=0 → λ₁; else μ−ω), both subtractions in Int. These are the conjecture's actual objects.

Decisive theorems:
- `partitionsFour_complete : ∀ parts, IsPartition 4 parts → parts ∈ partitionsFour` — exhaustive classification of arbitrary lists (length ≤ 4 by positivity, then case analysis), so the enumeration is not a sampled list. This directly cures the defect that got this author's PRs #286–288 rejected (objects absent); here the full partition set is present and proved complete, with `partitionsFour_nodup` and `partitionsFour_exact`.
- `RankCrankEquidistribution : ∀ (n : Nat) (allParts : List (List Nat)), allParts.Nodup → (∀ parts, parts ∈ allParts ↔ IsPartition n parts) → ∀ value : Int, |rank-fiber| = |crank-fiber|` — a faithful, enumeration-independent formalization of the conjecture's equidistribution claim.
- `conjecture7292_counterexample : ¬ RankCrankEquidistribution` — proved at n=4 via `rank_four_frequency : frequency rank 4 = 0` and `crank_four_frequency : frequency crank 4 = 1`.
- Supplementary `not_equal_supports` refutes even the weaker support-equality using existentials over all partitions.

Hypotheses: the counterexample uses ordinary partitions of 4, which trivially satisfy the conjecture's hypotheses; nothing vacuous. The Jacobi-triple-product clause is untouched, but negating the equidistribution conjunct suffices to refute the stated conjunction, and the report says so explicitly. LaTeX table matches Lean's `rank_values`/`crank_values` exactly; report's N(4,4)=0 ≠ 1=M(4,4) matches.
## Issues found
- none blocking (minor: `rank` uses `headD 0`, irrelevant since only nonempty lists are partitions of 4).
## Verdict rationale
The Lean project proves, from the standard definitions of Dyson rank and Andrews–Garvan crank, that the two statistics have different fiber cardinalities on the completely enumerated partitions of 4, negating a faithful universal formulation of the conjecture's equidistribution clause. Everything compiles and runs fresh with warnings-as-errors, no forbidden constructs, and both the JS auxiliary check and my independent recomputation confirm the mathematics. A genuine disproof.

## Disposition
APPROVED — merged into main (PR 338). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
