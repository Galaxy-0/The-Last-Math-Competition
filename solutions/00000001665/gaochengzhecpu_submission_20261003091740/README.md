# Disproof of conjecture 00000001665

**Result:** Disproof under the reading stated below.

The Cartesian product of the Petersen graph with P_2 has 20 vertices and a legal four-round burning sequence. The claimed equality would instead require ceil(sqrt(20)) + 1 = 6 rounds. The submission refutes that tight-family clause.

## The conjecture

> Definition: The burning number b(G) of a graph G is the minimal number of rounds needed to burn all vertices progressively. Conjecture: b(G) ≤ ⌈√n⌉ + 1 (paths attain ⌈√n⌉); the characterization of tight examples: Cartesian products of the Petersen graph with paths have burning number ⌈√n⌉ + 1, with no higher-order tight family.

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000001665.md); both languages are in `SOURCE.md`.

## Reading and scope

Refutes the asserted tight Cartesian-product family, independently of a universal upper-bound claim.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `not_tight_family_claim`, `product_encoding`, `all_burned`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
