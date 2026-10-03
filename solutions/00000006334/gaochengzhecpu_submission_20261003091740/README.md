# Conjecture 00000006334: disproof submission

An odd-order weighing matrix W(7,4).

Submitter: **gaochengzhecpu**. AI-assisted with Codex; draft for mathematical review.

## Scope

Directly refutes the source's explicit assertion that the matrix order is even, using a fully verified W(7,4). This main disproof does not depend on an interpretation of the undefined existence window. The previous W(4,3) witness remains as a separate window-bound observation.

Read `proof.pdf` for the complete ordinary proof, explicit assumptions and the correspondence to `Main.lean`. The LaTeX source is `proof.tex`. This revised version has been checked locally; its draft status does not imply organizer acceptance.

## Reproduce

Use Lean **4.19.0**, then run in this directory:

```text
lake build
```

Only Lean's bundled standard libraries are needed; there is no Mathlib dependency. The Lake configuration treats warnings as errors. Principal declarations print their axiom dependencies. Local checks found no `sorry`, `admit`, `native_decide` or added axioms; only standard Lean foundational axioms occur. `lean-verification.txt` records the successful local build.

Rebuild the PDF with `tectonic proof.tex` (or a standard LaTeX toolchain).

## Provenance and local validation

Original statement: [conjecture 00000006334](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/efab34b80a63963991d6c7ed625442a89a328a44/conjectures/00000006334.md). An unchanged bilingual copy is included as `SOURCE.md`.

Lean compilation, exact source correspondence, AI cross-review, and rendered-PDF inspection were completed locally. The source hashes in `verification.json` identify the checked artifacts. This is a draft submission, not an official review or an accepted result.

Immediately before preparing this submission, official metadata did not mark this conjecture solved, and no matching conjecture number was found in the titles or bodies of the 298 public PRs checked at 2026-10-03T13:15:11.955212+00:00. This limited check is not a claim of mathematical novelty or priority.

## Second review and correction

Second adversarial review identified an avoidable interpretation issue in the original window-bound argument. The strengthened main proof now uses an explicit odd-order W(7,4) to contradict the stated parity condition; all entries and Gram products are verified.
