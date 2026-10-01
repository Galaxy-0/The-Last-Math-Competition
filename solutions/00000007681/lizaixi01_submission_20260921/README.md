# Rule-3 submission: 00000007681

Submitted by GitHub user @lizaixi01. Prepared with AI assistance using OpenAI Codex; mathematical reasoning, Lean code, and documentation were AI-assisted. Acceptance and scoring are determined by the organizers.

## Mathematical scope

The displayed interlacing assertion is false under standard continuous q-Hermite normalization H0=1, H1=2x. The source omits these initial values. The later monotonicity assertion is not separately settled.

This is an elementary counterexample to the generated statement, not a claim of novel mathematical theory or worldwide priority. The complete 100-PR title/body snapshot and PR6's detailed triage/campaign files contained no matching problem identifier at the recorded check time; unnumbered text, all comments, forks, and unpublished work are not exhaustively covered.

Original source revision: `95acb520ec5607c826b8a997b1ef2fc82d6f7c57`.
Source: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/95acb520ec5607c826b8a997b1ef2fc82d6f7c57/conjectures/00000007681.md

## Required materials

- `proof.tex`: actual LaTeX source.
- `proof.pdf`: PDF compiled from that source with official portable Tectonic 0.17.0 and visually checked.
- `lean/`: complete source project, official Lean toolchain pin, fixed dependency manifest and source-lock bootstrap.
- `STATEMENT_MAP.md`, `SEMANTIC_REVIEW.md`, `evidence/`: correspondence, independent model review and actual command outputs.

## Reproduce Lean

Install the official Lean version in `lean/lean-toolchain` (4.33.0), Python 3, and Git. Run from `lean/`:

```text
python bootstrap.py
lake exe cache get Mathlib.Algebra.Polynomial.Degree.SmallDegree Mathlib.Algebra.Polynomial.Eval.Defs Mathlib.Analysis.Real.Sqrt Mathlib.Tactic.FinCases Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
lake build +Results
lake env lean Audit.lean
lake env leanchecker --fresh --verbose Results
```

The bootstrap verifies or downloads the exact mathlib and eight dependency commits in `dependencies.lock.json`; it refuses modified or mismatched existing sources. The mathlib path in the Lake file is populated by this bootstrap. Do not run `lake update` to silently change the locked dependency set. Network access is needed on a fresh machine. The large toolchain and cache are intentionally not bundled.

Targets: `Counterexample7681.conjectured_interlacing_false; Counterexample7681.full_conjecture_false`.
Only `propext`, `Classical.choice`, `Quot.sound` are allowed in the audit. Official `leanchecker --fresh` replays the official kernel; it is not an independently implemented external kernel. The completed round-wide fresh replay and this package's own build/audit are recorded in `VALIDATION.md` and `evidence/`.

## Reproduce PDF

Compile `proof.tex` using a normal LaTeX installation with amsmath, amssymb, amsthm, geometry and hyperref; for example `tectonic --untrusted proof.tex`. Initial TeX bundle downloads may require network access. Final compilation logs and visual QA are included.

## Attribution and license

Upstream statement is reproduced with its GPL-3.0 license in `LICENSE`. This submission's source is offered under the same license for repository compatibility; Lean/mathlib and other dependencies retain their own licenses and are not vendored here. Attribution uses the submitter's GitHub handle; no institutional affiliation is claimed.

Public packaging: proof.tex, proof.pdf, and all Lean project files are byte-identical to the validated originals. Machine-specific absolute paths in evidence have been replaced with placeholders; this is documented in PUBLICATION.md. The semantic review is an AI-model review, not an independent human review.
