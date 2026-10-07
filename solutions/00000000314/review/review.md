# Solution Review — Conjecture 00000000314 (PR 694)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005123312`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000000314.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** extracted text of shipped vs rebuilt PDF agrees after normalization; only glyph/ligature/math-font extraction artifacts, no content differences.
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/declared `axiom`. Re-ran `lake env lean Axioms.lean`: `C314.conjecture314_false` depends only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` and `build.txt` reproduce my runs exactly; `SHA256SUMS.txt` has a stale `conjecture.md` entry (actual file matches the official conjecture byte-for-byte).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000000314/Jackmeson1_submission_20261005123312/`; no existing solution on `main`.

## Semantic audit

The conjecture asserts that `{M(√p) : p prime}` is dense in `[√5, 3)`, where the text defines `M(α) = limsup 1/‖qα‖`. The text's formula is ambiguous: as printed there is no factor `q` (the literal reading), while the standard Lagrange/Markov value is `limsup 1/(q‖qα‖)`. The submission formalizes both readings and refutes density under each — exactly the right way to handle this ambiguity.

The engine is Pell's equation. `pell_large` uses Mathlib's `Pell.IsFundamental` to produce solutions of `x² − p y² = 1` with `y` beyond any bound (the fundamental unit's powers have strictly increasing `y`); `pell_bound` shows `‖y√p‖ · 2y√p ≤ 1` (from `(x − y√p)(x + y√p) = 1` and `0 < x − y√p`), so `1/‖q√p‖ ≥ 2q√p` for arbitrarily large `q`. Under the literal reading the limsup is therefore `⊤` for every prime `p`; under the standard reading `M(√p) ≥ 2√p ≥ 2√2` (primes are ≥ 2). Since `√5 < 2√2 < 3`, the nonempty open subinterval `(√5, 2√2)` of `[√5, 3)` contains no value in either reading.

Density is refuted in two robust senses: topological (`[√5,3) ⊆ closure S` fails since `closure S ⊆ [2√2,∞]` is closed and excludes `√5`) and interval-based (every `a < b` in the interval has a value strictly between — fails for `a = √5`, `b = 2√2`). Both are proved for both readings of `M`, in `ℝ≥0∞` so that the literal reading's infinite values are representable. I verified the mathematics independently: quadratic irrationals have Markov/Lagrange values bounded below by `2√2` (indeed `√(4+1/p)`-type values), so a density claim on `[√5,3)` — the classical initial part of the Lagrange spectrum — cannot be witnessed by prime square roots alone. The second conjunct ("the density follows from the transition statistics of the continued-fraction partial quotients") presupposes the density and falls with it; the submission says so explicitly.

## Issues found

- Minor hygiene: stale `conjecture.md` hash in `verification/SHA256SUMS.txt`; the shipped file is correct.
- No other issues. The report honestly flags that the refutation uses the value floor `2√2` rather than the exact Markov values, which is all the density clause needs.

## Verdict

APPROVED. A decisive, doubly-robust disproof (both readings of the definition, both senses of density), with a machine-checked Pell mechanism, clean build and axioms, and a report that faithfully mirrors the Lean development.
