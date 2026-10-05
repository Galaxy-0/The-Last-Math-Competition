# TLMC 00000007885: disproof of the binary partition matching clause

The final combinatorial assertion is false for ordinary binary partitions (unordered partitions into powers of two, with repeated parts allowed). The product

\[
\prod_{k\ge0}(1+t^{2^k})=\sum_{n\ge0}t^n
\]

has every coefficient equal to 1, whereas the binary partition count at 2 is 2, from `{2}` and `{1,1}`.

The Lean project proves the complete finite-product identity
`P_K = sum_{n < 2^K} X^n`, its full coefficient formula, and coefficientwise eventual stabilization. It defines binary partition numbers by filtering Mathlib's `Nat.Partition n`, explicitly enumerates all partitions of 2, and proves the mismatch both for the infinite coefficient sequence and for every finite truncation `K >= 2`.

Main theorem: `BinaryPartitionMismatch.conjecture_00000007885_false : ¬ BinaryPartitionMismatch.MatchingClause`. Equivalent sequence statement: `BinaryPartitionMismatch.coefficient_sequences_ne : infiniteProductCoeff ≠ binaryPartitionNumber` (in the same namespace).

All audited theorems compile and use only `propext`, `Classical.choice`, and `Quot.sound`. There are no admitted proofs or additional axioms. Numerical checks are supplementary and are not needed for the formal proof.

## Contents

- `lean4/BinaryPartitionMismatch.lean`: complete formalization, verbatim conjecture in the opening documentation, and axiom audits.
- `lean4/lean-toolchain`, `lean4/lakefile.toml`, `lean4/lake-manifest.json`: self-contained project pinned to Lean and Mathlib `v4.33.0`.
- `report.tex`, `report.pdf`: full mathematical proof, interpretation discussion, Lean statements, semantic correspondence, and axiom audit.
- `verification.txt`: successful compiler output and axiom audit and the independent Python checks.
- `verify.py`: standard-library finite-product multiplication, binary partition enumeration, and dynamic-programming sanity checks.

## Build

From a fresh copy with Lean's `elan` installed:

```sh
cd lean4
lake exe cache get && lake build
cd ..
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Mathlib is pinned to tag `v4.33.0`, commit `db584cd6d46c92f209a44c0f1c829460d327499d`. Lean compilation succeeded with the pinned versions.

## Reading and scope

“Binary partition numbers” is taken in the standard sense, OEIS A018819: partitions into powers of 2, with repetitions allowed. With **distinct** powers of 2 the count is 1 in every degree, equal to the product's coefficient, so that matching clause would be trivially true. The conjecture's identification of the product with binary partition numbers makes the standard unrestricted sense the faithful reading. The Lean formalization proves the failure of that combinatorial equality.

## Sphere-spectrum remark — human proof, not formalized

Standard THH satisfies `THH(S) ≃ S`, because the sphere is the unit of the smash product, so `THH(S) ≃ S ∧_(S∧S) S ≃ S`. Consequently every iterate is equivalent to `S`, and its p-completed homotopy grading is independent of the iterate. For an invariant ordinary graded count that records these groups, `P_(n+1) = P_n`; combining this with the doubling law gives `P_n · t^(2^n) = 0`. Multiplication by a monomial shifts coefficients injectively in integer polynomials and formal power series, so `P_n = 0`, contradicting the nonzero degree-zero group `π_0(S_p^∧) = Z_p`. The argument assumes the same grading and counting rule for every iterate and that the count records nonzero `π_0`; the report states this scope explicitly.

Reference: T. Nikolaus and P. Scholze, *On topological cyclic homology*, *Publications mathématiques de l'IHÉS* **129** (2019), 219–353, Example II.1.2(ii) and Definition III.2.3, https://doi.org/10.1007/s10240-019-00104-9 ([arXiv:1707.01799](https://arxiv.org/abs/1707.01799)). This topological argument is cited and explained as a human proof; it is **not formalized** and supplies no hypothesis to the Lean partition proof.

Submitted by AlyciaBHZ on behalf of the Omega Institute (trureturing project, https://github.com/the-omega-institute/trureturing).

No trureturing code has been vendored.
