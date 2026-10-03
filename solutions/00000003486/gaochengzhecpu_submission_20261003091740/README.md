# Disproof of conjecture 00000003486

**Result:** Disproof under the reading stated below.

Two nonisomorphic four-critical graphs on seven vertices have the same vertex-deletion chromatic spectrum: every entry is 3. The proof verifies criticality for every proper subgraph and disproves the proposed minimum of thirteen vertices without claiming the true minimum.

## The conjecture

> Definition: Reconstruction of critical graphs: reconstructing the original graph from the chromatic-spectrum information of single-vertex deletions. Conjecture: There exist pairs of four-critical graphs with identical single-deletion chromatic spectra yet non-isomorphic graphs; the minimal counterexample pair has thirteen vertices, and the complete list of counterexample families is a finite slice of the generalized Mycielski framework. (critical reconstruction counterexample)

[Original statement](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000003486.md); both languages are in `SOURCE.md`.

## Reading and scope

Four-critical means every proper subgraph is three-colorable; the construction refutes minimum thirteen without asserting the true minimum.

## Proof

The full mathematical argument is in [main.pdf](main.pdf), with LaTeX source [main.tex](main.tex).

## Formalization

Lean **4.19.0**, using its bundled standard library only; no Mathlib dependency. The complete project is in `lean/`, with warnings treated as errors. The report explains how the encoded objects and final proposition correspond to the original statement.

Audited declarations include `not_minimum_thirteen_consequence`, `G_four_critical`, `H_four_critical`, `same_deletion_spectrum`, `graphs_not_isomorphic`. `lean-verification.txt` records the clean build and printed axiom dependencies. No `sorry`, `admit`, `native_decide`, or additional axiom is used; only standard Lean foundational axioms occur.

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
