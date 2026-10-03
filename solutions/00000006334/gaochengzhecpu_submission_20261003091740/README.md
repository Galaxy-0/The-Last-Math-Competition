# Disproof of conjecture 00000006334

**Result:** Disproof under the reading stated below.

The 7 x 7 circulant matrix with first row (1,-1,-1,0,-1,0,0) has entries in {0,1,-1} and satisfies WW^T = 4I_7. This odd-order W(7,4) contradicts the source's explicit even-order requirement; it also satisfies 4 + 2 <= 7.

## The conjecture

> Definition: Weighing matrices are the weighted orthogonal type. Conjecture: The conversion constant is explicit in the existence window of the weight, the necessary and sufficient condition being the square decomposition of the weight; the sum of the decomposition is the matrix order, even; and the lower bound of the window is weight plus two, attained by conference types. (square-decomposition conversion of weight existence windows)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000006334.md); both languages are in `SOURCE.md`.

## Reading and scope

Directly refutes the source's explicit assertion that the matrix order is even, using a fully verified W(7,4). This main disproof does not depend on an interpretation of the undefined existence window. The previous W(4,3) witness remains as a separate window-bound observation.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `C4_is_weighing`, `C4_is_conference`, `claimed_necessary_bound_false`, `conference_bound_false`, `full_bound_conjecture_false`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
