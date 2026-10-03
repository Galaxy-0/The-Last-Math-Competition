# Disproof of conjecture 00000008544

**Result:** Disproof under the reading stated below.

In the product of three two-element chains, the weight-one and weight-two layers are distinct antichains of size three. A partition into three chains proves that both are maximum, so the asserted uniqueness fails.

## The conjecture

> Definition: A chain product lattice is the Cartesian product of total order chains. Conjecture: The Sperner number of a chain product lattice is the maximum multinomial coefficient; and the maximal antichain is unique, namely the middle layer. (uniqueness of chain product Sperner)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000008544.md); both languages are in `SOURCE.md`.

## Reading and scope

Verifies maximum, rather than merely maximal, antichains and covers every subset.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `every_subset_encoded`, `cube_left_inverse`, `cube_right_inverse`, `sharp_upper_bound`, `conjecture8544_false`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
