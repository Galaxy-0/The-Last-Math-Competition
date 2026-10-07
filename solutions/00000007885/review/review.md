# Solution Review — Conjecture 00000007885 (PR 628)

**Submission:** AlyciaBHZ — `solutions/00000007885/AlyciaBHZ_submission_20261005101836`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

| Check | Result |
|---|---|
| Official conjecture read (`conjectures/00000007885.md`, bilingual) | pass |
| LaTeX report read in full; rebuilt with `latexmk -pdf` | pass |
| Shipped vs rebuilt PDF text (pypdf, glyph-normalized) | pass |
| `lake build` (Lean v4.33.0, Mathlib db584cd6d4, prebuilt pool) | pass |
| Axiom audit (`#print axioms`, scratch checks; allowed set only) | pass |
| `verify.py` executed; output matches shipped `verification.txt` | pass |
| No `sorry`/`native_decide`/`admit`/`extern`/`unsafe`/`axiom` | pass |
| Faithfulness gate (conjecture's own objects, no surrogate) | pass |
| Semantic audit (exact quantifiers/objects) | pass |

Build facts: `lake build` exits 0 with no errors; the only reported axioms are
`propext`, `Classical.choice`, `Quot.sound` for this PR every audited theorem depends only on `propext`, `Classical.choice`, `Quot.sound`; the Lean source
SHA-256 in `verification.txt` matches the shipped source; the rebuilt PDF has the
same page count as the shipped one and identical extracted text modulo
ligature/smart-quote glyph-extraction artifacts introduced by font subsetting.

## Semantic audit

Decisive theorem conjecture_00000007885_false is the exact negation of MatchingClause := forall n, infiniteProductCoeff n = binaryPartitionNumber n, instantiated at n=2 with 1 != 2, both sides computed from the conjecture's own displayed product and the standard partition count. The infinite product is defined by coefficientwise stabilization with a proved independence lemma, not stipulated. THH itself is not formalized (infeasible in Mathlib and unnecessary for this clause).

## Issues found

None blocking. Scope note: the submission refutes the stated combinatorial clause rather than proving anything about THH^{(n)}(S); given the conjecture asserts that clause as a consequence and the clause is false under the standard reading, the conjecture as written is false. The distinct-parts reading is explicitly discussed and not hidden.

## Verdict

**APPROVED** — disproof.

The conjecture's final explicit clause asserts that the dimension generating function equals prod_{k>=0}(1+t^{2^k}) 'matching the binary partition numbers'. Under the standard meaning of binary partition numbers (unordered partitions into powers of two with repetition, OEIS A018819) this is false: every coefficient of the product is 1 (the product is 1+t+t^2+... by uniqueness of binary expansion), while b(2)=2 (partitions {2} and {1,1}). The Lean file formalizes the actual polynomial products in Polynomial Nat with a proved full coefficient formula and truncation-independent stabilization, and exhaustively classifies Nat.Partition 2 to get b(2)=2 exactly (not just witnesses). The report honestly scopes the refutation to the matching clause, shows the distinct-parts reading would make the clause trivially true, and adds a flagged, non-formalized human observation that THH(S)=~S forces any invariant graded count to satisfy P_{n+1}=P_n, contradicting the doubling law - so the disproof is not merely terminological. Faithful: the clause formalized is the conjecture's own; its negation at n=2 refutes the conjunction.
