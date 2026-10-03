# Disproof of conjecture 00000008536

**Result:** Disproof under the reading stated below.

In the Boolean lattice on the six edges of K_4, the four vertex stars generate all singletons by pairwise intersection and then every subset by union. The lattice has six join-irreducibles but needs at most four generators, contradicting the asserted equality.

## The conjecture

> Definition: A distributive lattice is a lattice of ideals. Conjecture: The minimal number of generators of a distributive lattice equals its number of join-irreducible elements; and the dimension of the Boolean lattice into which a distributive lattice embeds equals its minimal number of generators. (embedding dimension of distributive lattices)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000008536.md); both languages are in `SOURCE.md`.

## Reading and scope

Lattice generation uses both binary meet and join, even without free constants; join-only generation would be a different claim.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `booleanSix_is_distributive_lattice`, `join_irreducibles_exact`, `four_generators_suffice`, `conjecture8536_false`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
