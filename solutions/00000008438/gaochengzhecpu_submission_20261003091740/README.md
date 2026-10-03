# Disproof of conjecture 00000008438

**Result:** Disproof under the reading stated below.

The array whose columns are all 27 ternary triples has three rows, three symbols, strength three, and index one. Its columns are distinct, while 27 > 3^2 - 3 + 3 = 9, contradicting the proposed column bound.

## The conjecture

> Definition: The strength t of an orthogonal array: the uniformity of any t rows. Conjecture: The maximal number of columns of a strength-t OA is N(n,t) at most n^2 - n + t; the bound is attained when n is a prime power; and for non-prime-powers the deficit is at least n^{1/2}. (maximal column count of orthogonal arrays)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000008438.md); both languages are in `SOURCE.md`.

## Reading and scope

Includes a ternary example with both row count and alphabet size three, eliminating that possible ambiguity.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `ternaryArray_columns_distinct`, `conjecture8438_false_ternary`, `binaryArray_is_OA3`, `binaryArray_columns_distinct`, `conjecture8438_false`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

## Reproduce

From this submission directory:

```text
cd lean
lake build
```

From this submission directory, rebuild the PDF with:

```text
tectonic main.tex
```

## Submission status

AI-assisted with Codex; submitted by **gaochengzhecpu**. The statement-to-proof correspondence was checked locally by a separate agent, and the PDF was rendered and inspected. This remains a draft for independent mathematical review; local verification is not organizer acceptance. `verification.json` gives hashes of the reviewed files.
