# Solution Review — Conjecture 00000000038 (PR 454)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004115044`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read; `SOURCE.md` is byte-identical to the official file.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded. Shipped and rebuilt PDFs both contain two pages with identical extracted semantic content and no TeX warnings.
- Lean: official pinned dependencies were linked, then fresh `lake build` and direct `lake env lean -DwarningAsError=true Main.lean` succeeded under Lean 4.19.0/Mathlib `c44e0c8e...`.
- Axioms: all five printed results depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary programs: none supplied or needed; arbitrary lengths and interval sizes are proved directly.
- Base metadata marks the conjecture unsolved.

## Semantic audit
For any list of length at least two with all entries at least 3, product strictly exceeds sum. The base inequality follows from `(u-1)(v-1)-1>0`, and induction gives the general list inequality without any distinctness assumption, so repetitions remain allowed. For each N≥4, `A_N={3,...,N}` lies in `[N]`, has cardinality N-2, and density at least 1/2. Therefore `A_N` has no sum-product identity of any nontrivial length. This simultaneously refutes every possible choice of `k(1/2)`, even if k depends on N or A.

The only remaining identities are singleton identities `x=x`, which both source languages explicitly exclude as trivial; admitting k=1 would make the conjecture immediate for every set. Lean strengthens the semantic defense by proving that any equality for entries in `A_N` forces list length one. Its final theorem also refutes an eventual-in-N weakening, and its arbitrarily-large-family theorem rules out an appeal to sufficiently large N. Lists, finite intervals, cardinalities, real density, strict inequality, and final quantifier negation all use their ordinary meanings.

## Issues found
None blocking.

## Verdict
APPROVED. The family `{3,...,N}` provides arbitrarily large density-1/2 sets with no sum-product identities except trivial singletons, and all independent LaTeX, Lean, axiom, path, and semantic checks pass.
