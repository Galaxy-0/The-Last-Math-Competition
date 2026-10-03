# Disproof of conjecture 00000008535

**Result:** Disproof under the reading stated below.

The two-element Boolean lattice is supersolvable and geometric. Its characteristic polynomial, calculated from the defining Mobius recurrence, is t - 1 and has the positive root 1. Thus the claimed negativity of every root fails.

## The conjecture

> Definition: The characteristic polynomial of a lattice is the generating function of its Mobius function. Conjecture: The roots of the characteristic polynomial of a geometric lattice are real and negative when the lattice is supersolvable; and in general the minimum of the modulus spectrum of roots is controlled by the Mobius absolute value of its minimal antichain. (real-rootedness and modulus bound of characteristic roots)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000008535.md); both languages are in `SOURCE.md`.

## Reading and scope

Uses the standard characteristic-polynomial convention; a positive integer root is also a positive real root.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `booleanOne_geometric`, `booleanOne_supersolvable`, `mobius_correct`, `conjecture8535_false`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
