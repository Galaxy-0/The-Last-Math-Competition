# Disproof of conjecture 00000003490

**Result:** Disproof under the reading stated below.

At every positive integer k, a chromatic polynomial counts proper k-colorings. A graph's chromatic number is the least k for which that count is positive. Therefore two graphs with the same chromatic polynomial cannot have different chromatic numbers.

## The conjecture

> Definition: Mutual determinacy of the chromatic polynomial and spectral radius: the separation power of joint invariants. Conjecture: There exist graph families with identical chromatic polynomial and spectral radius but different chromatic numbers; the minimal order of the separating family is ten, with the separation realized by asymptotic isomorphism of Schwenk-type branch pastings. (polynomial-spectrum separating family)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000003490.md); both languages are in `SOURCE.md`.

## Reading and scope

A general theorem for arbitrary finite graphs; not only a bounded search.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `not_separating_pair_claim`, `not_polynomial_separating_pair_claim`, `evaluation_pos_iff_colorable`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
