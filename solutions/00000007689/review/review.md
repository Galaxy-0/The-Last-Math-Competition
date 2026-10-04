# Solution Review — Conjecture 00000007689 (PR 362)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "a_{r,s} (Bailey sliding-chain count) satisfies the Delannoy recursion and equals D(r,s); the diagonal grows as a_{m,m} ~ c·3^m·m^{-1/2}; and the minimal product-side factor count at level (r,s) is r+s+1."
- LaTeX: recompiled twice with pdflatex, exit 0; shipped main.pdf is a real PDF matching the tex.
- Lean build: fresh `rm -rf .lake && lake build`, exit 0, zero warnings (`-DwarningAsError=true`), Lean 4.19.0, `Std` only. Uses `maxHeartbeats`/`maxRecDepth` options (legitimate compile options, not kernel bypasses).
- Forbidden content: none — grep for sorry/admit/native_decide/axiom decls/unsafe/implemented_by/extern/skipKernelTC found nothing. `#print axioms` for both key theorems = [propext, Quot.sound].
- Auxiliary code: no Python/JS shipped; verification/ holds build logs (exit 0) and review records consistent with my fresh build. Independently re-derived in python3: D(2,2)=13, D(10,10)=8,097,453 (cross-checked with binomial formula Σ C(n,k)C(n+k,k)); block growth 13·D(r,s) ≤ D(r+2,s+2) for all r,s ≤ 40; 13^n ≤ D(2n,2n) for n ≤ 25; (4n+9)·9^n ≤ 9·13^n for n ≤ 60; D(m,m)/3^m = 6.9 → 137 → 3111 → 74723 (m=5,10,15,20), growth constant → 3+2√2 ≈ 5.828 — confirming the diagonal is not O(3^m).
## Semantic audit
The conjecture literally asserts three conjuncts; the first two are jointly unsatisfiable. Clause 1: a_{r,s} = D(r,s), the Delannoy numbers defined by the stated recursion. Clause 2: a_{m,m} ~ c·3^m·m^{-1/2} with the Chinese explicitly calling this "中心 Delannoy 增长" (central Delannoy growth). But the true central-Delannoy growth constant is 3+2√2 ≈ 5.83 > 3 (my computation confirms), so clause 1 implies the diagonal is NOT O(3^m), while clause 2 (finite positive c) implies the eventual integer bound a_{m,m} ≤ C·3^m. No array satisfies both — the refutation is interpretation-independent, as the tex claims ("the contradiction does not depend on any interpretation of the Bailey sliding construction").

Lean encodes the actual objects: `def D : Nat → Nat → Nat` by the genuine terminating Delannoy recurrence `| 0, _ => 1 | _, 0 => 1 | r+1, s+1 => D r (s+1) + D (r+1) s + D r s` (exactly the conjecture's recursion with the standard boundary); `recursion_unique` proves any array obeying the boundary conditions and recursion equals D, so equality-to-D is not a smuggled definition but forced by the conjecture's own clause. Key theorems: `block_growth : 13 * D r s ≤ D (r+2) (s+2)`, `all_diagonal_lower_bounds : 13^n ≤ D (2*n) (2*n)`, `bernoulli_bound : (4*n+9)*9^n ≤ 9*13^n`, and decisively

`theorem no_eventual_three_power_bound : ¬ ∃ C N : Nat, ∀ m : Nat, N ≤ m → D m m ≤ C * 3^m`

`theorem conjecture7689_counterexample (a : Nat → Nat → Nat) : ¬ NecessaryAssertions a`

with `NecessaryAssertions a := (∀ r s, a r s = D r s) ∧ ∃ C N, ∀ m ≥ N, a m m ≤ C * 3^m`. Both conjuncts are consequences of the conjecture's clauses 1 and 2 respectively (clause 2 gives the bound with integer C ≥ 2c; nonpositive c is separately excluded in the tex since it cannot asymptotically match a positive sequence). Refuting their conjunction refutes the conjecture. The real-asymptotic → integer-bound bridge is prose-only in the tex, but it is elementary, explicitly disclosed, and one-directional in the safe direction (the Lean refutes the weaker necessary consequence). Not vacuous: D is the real Delannoy function, all statements are universally quantified over arbitrary indices with no finite-table extrapolation. Clause 3 (r+s+1 factor count) is untouched, correctly, since the conjunction already fails.
## Issues found
none blocking
- Disclosed interpretation call: the real asymptotic clause is refuted via its necessary integer O(3^m) consequence rather than a Lean formalization of ~; this is sound and disclosed in main.tex.
## Verdict rationale
The submission proves, from the conjecture's own Delannoy recursion, that the diagonal grows at least like (√13)^m ≈ 3.606^m and hence admits no eventual C·3^m bound, directly contradicting the asserted c·3^m·m^{-1/2} asymptotic — I independently confirmed the growth constants and every lemma numerically. The Lean builds clean from scratch with only standard logical axioms, the LaTeX report matches, and the refutation engages the conjecture's actual objects (the genuine Delannoy numbers and the actual asymptotic claim) rather than proxies.

## Disposition
APPROVED — merged into main (PR 362). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
