# Disproof of conjecture 00000004274

**Result:** Disproof under the reading stated below.

Every automorphism of C_7 is multiplication by one of its six nonzero residues, and these automorphisms commute. The center of Aut(C_7) therefore has order 6, which is not a product of powers of 2 with nonnegative integer exponents.

## The conjecture

> Definition: The center of the automorphism group of a countable p-group consists of the elements commuting with all automorphisms. Conjecture: The center is nontrivial if and only if a characteristic element exists, the count of central elements is read off explicitly from the Ulm sequence, and the formula is a termwise product of powers of 2. (counting the automorphism center of p-groups)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000004274.md); both languages are in `SOURCE.md`.

## Reading and scope

Power-of-two exponents use the usual nonnegative-integer/cardinal counting interpretation; the source does not specify the exponent domain.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `centerEnumeration_nodup`, `seven_prime`, `conjecture04274_false`, `full_conjecture_false`, `center_has_six_elements`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
