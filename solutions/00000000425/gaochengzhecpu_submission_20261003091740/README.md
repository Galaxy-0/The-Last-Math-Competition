# Disproof of conjecture 00000000425

**Result:** Disproof under the reading stated below.

For the equal-sided 2 x 2 x 2 MacMahon box, the coefficient sequence starts 1, 1, 3, so a_1^2 = 1 < 3 = a_0 a_2. Lean constructs the formal quotient, proves its numerator/denominator coefficient equation at every index, and derives this failure directly.

## The conjecture

> Definition: The generating function of boxed plane partitions is MacMahon's three-parameter product. Conjecture: The coefficient sequence of the diagonal specialization always satisfies coefficientwise log-concavity; and equality in the concavity holds only at the diagonal single cell. (diagonal coefficient log-concavity)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000000425.md); both languages are in `SOURCE.md`.

## Reading and scope

Interprets diagonal specialization as equal box side lengths. The Lean proof now constructs the infinite MacMahon formal quotient, proves its full numerator/denominator equation, and directly refutes log-concavity. The cross-size polynomial reading is additionally addressed in ordinary mathematics.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `macmahon_cube_two_not_logconcave`, `counting_matches_macmahon_prefix`, `formalQuotient_spec`, `macMahonCubeTwo_spec`, `macmahon_product_counterexample`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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

Independent arithmetic check: `python verify.py`.

## Submission status

AI-assisted with Codex; submitted by **gaochengzhecpu**. The statement-to-proof correspondence was checked locally by a separate agent, and the PDF was rendered and inspected. This remains a draft for independent mathematical review; local verification is not organizer acceptance. `verification.json` gives hashes of the reviewed files.
