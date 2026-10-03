# Disproof of conjecture 00000002617

**Result:** Disproof under the reading stated below.

For the incidence algebra of the two-element chain over F_2, the strictly upper triangular matrix unit belongs to every maximal left ideal and is nonzero. Thus the Jacobson radical is nonzero, contradicting the asserted radical property.

## The conjecture

> Definition: Incidence algebras of locally finite posets: the structure of convolution algebras. Conjecture: The Jacobson radical of an incidence algebra is zero, with semisimplicity evidenced by pointwise invertibility of the Möbius function; the vanishing of the radical follows from local finiteness of the unit decomposition. (incidence algebra semisimplicity)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000002617.md); both languages are in `SOURCE.md`.

## Reading and scope

Jacobson radical is the intersection of all maximal proper left ideals, not a surrogate nilpotence test.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `not_zero_radical_claim`, `ring_laws`, `multiplication_is_convolution`, `every_incidence_function`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
