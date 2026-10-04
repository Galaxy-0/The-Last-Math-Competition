# Solution Review — Conjecture 00000002839 (PR 351)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — "the closure dimension of a generic n-point sample is min(n−1, d), and the minimal degree of the closure ideal is an explicit function of sample size" (Zariski closures of finite samples).
- LaTeX: recompiled twice with pdflatex, both exit 0, 1 page; shipped main.pdf is a real PDF 1.5 whose gs-extracted text matches main.tex.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings, Lean 4.19.0, deps: Std only.
- Forbidden content: none — grep for sorry/admit/native_decide/axiom/unsafe/implemented_by/extern/skipKernelTC empty; `#print axioms` shows only [propext] / [propext, Quot.sound] (both standard logical axioms).
- Auxiliary code: no Python/JS shipped; none claimed. verification/lean-axioms.log consistent; VALIDATION.json independent_review PASS.
## Semantic audit
Conjecture (bilingual; conjecture.md byte-identical, SOURCE.md identical modulo CRLF): closure dimension of a generic n-point sample = min(n−1, d). Lean encodings:

- `structure DomainData K` — full integral-domain laws; theorems are universally quantified over it, so they hold over every field, in particular every algebraically closed field (the stated setting); `integerDomain : DomainData Int` proves the structure non-vacuous without restricting the universal theorems.
- `inductive Polynomial K` (constant/X/add/mul/neg) with `ofCoefficients`/`horner` and proved `coefficient_bridge` — genuine univariate polynomials, no degree truncation.
- `def ZariskiClosed D S := ∃ equations : Polynomial K → Prop, ∀ x, S x ↔ ∀ p, equations p → evaluate D x p = D.zero` — standard zero sets; `def closure D S := fun x => ∀ p, (∀ y, S y → evaluate D y p = 0) → evaluate D x p = 0` — the exact V(I(S)) definition, with `subset_closure`, `closure_is_closed`, `closure_minimal` proved.
- `IrreducibleClosedIn D ambient S` — nonempty closed subset with the arbitrary-closed-cover irreducibility condition; `DimensionAtLeast D T n := ∃ C : Fin (n+1) → PointSet K, (∀ i, IrreducibleClosedIn D T (C i)) ∧ ∀ i, ProperSubset (C i.castSucc) (C i.succ)` — standard chain/Krull dimension.
- `pair_closed` ({a,b} = V((X−a)(X−b)) using `product_zero_iff`), `pair_closure_exact (closure D (pair a b) = pair a b)`, `irreducibles_of_pair` (nonempty irreducible closed subsets of {a,b} are exactly the singletons), `pair_dimension_at_least_zero`, `pair_dimension_not_one`.
- Final: `theorem conjecture2839_false {K} (D : DomainData K) : ¬∃ a b : K, a ≠ b ∧ DimensionAtLeast D (closure D (pair a b)) (min (2-1) 1)` — at n=2, d=1 (affine line = K), the conjectured dimension is min(1,1)=1, but every distinct pair's closure has dimension exactly 0.

Mathematics verified: a finite subset of the affine line over a domain is V((X−a)(X−b)), equals its own closure, and its only nonempty irreducible closed subsets are singletons, so the strict-chain dimension is 0 ≠ 1. Since the refutation covers EVERY distinct two-point sample, no "generic locus" reading can rescue the formula (any nonempty generic locus of pairs contains a distinct pair). Interpretation calls disclosed: (i) the conjecture plausibly conflates Zariski closure with affine span (whose dimension would be min(n−1,d)) — the report explicitly addresses this and the bilingual text says Zariski closure (Zariski 闭包) in both languages; under the authoritative literal reading the formula is false. (ii) The minimal-degree clause is untouched, but refuting the dimension clause refutes the conjunction. (iii) Dimension is formalized via chains (≥ k), with both ≥0 and ¬≥1 established, i.e., dimension exactly 0. Not vacuous: universal negation with concrete consistency model.
## Issues found
none blocking
## Verdict rationale
Clean build, standard axioms only, faithful encodings of Zariski closure, irreducibility, and Krull dimension, and a decisive, essentially trivial counterexample (two-point sets are zero-dimensional) that no genericity reading can evade. The Zariski-closure-vs-affine-span ambiguity is disclosed in the report and the bilingual text is explicitly on the closure side.

## Disposition
APPROVED — merged into main (PR 351). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
