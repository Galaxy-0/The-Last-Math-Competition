# Solution Review — Conjecture 00000000307 (PR 683)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005112430`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000000307.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization (3-character extraction delta); no content differences.
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `Conjecture307.conjecture307_false` depends only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` and `build.txt` reproduce my runs; `SHA256SUMS.txt` has a stale `conjecture.md` entry (the shipped file matches the official conjecture byte-for-byte).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000000307/Jackmeson1_submission_20261005112430/`; no existing solution on `main`.

## Semantic audit

The submission's engine is a genuine two-dimensional Dirichlet theorem proved by pigeonhole in Lean (`dirichlet_two`): for all reals `x, y` and every `N ≥ 1` there are `1 ≤ q ≤ N²` and integers `p, r` with `|qx − p| < 1/N` and `|qy − r| < 1/N`. The proof (`N²+1` points `k ↦ (⌊N·fract(kx)⌋, ⌊N·fract(ky)⌋)` into `N²` boxes; `q = k − l`; the floor-difference identity) is standard and correctly executed; I re-verified the box count and the `1/N` bound.

"Weighted by `q^{1+i}`" admits two literal readings and both are formalized: reading B multiplies the nearest-integer errors `‖qx‖`, `‖qy‖` (the standard weighted-bad-approximability object), reading A multiplies `|x − p/q|`, `|y − r/q|` (equivalently weights `q^i` on `‖qx‖` — one power of `q` lower). In both, membership is `∃c > 0 ∀q ≥ 1 ∀p, r: c ≤ q^{1+i}·(first) ∨ c ≤ q^{1+j}·(second)`, i.e. the min-quantifier written as a disjunction over `p, r`, which is exactly `∀q: max ≥ c`. Full-dimensionality is `dimH = 2` on the Euclidean plane.

Clause (II) — "for every weighting with `i + j < 0` the intersection remains full-dimensional" — is refuted under the faithful reading B at the admissible weighting `i = j = −3/4` (sum `−3/2 < 0`): Dirichlet with `N = M²` gives `q ≤ M⁴` and both errors `< 1/M²`, so `q^{1/4}·error ≤ M/M² = 1/M < c` for every `c` — the set is empty and `dimH ∅ = 0 ≠ 2`. This kills the universal clause and hence the conjunction; the report states plainly that clause (I) under reading B is *not* refuted (indeed `BadB(0,0)` contains `Bad × ℝ`, consistent with Schmidt's classical full-dimension/winning result for `i + j = 0`). Under reading A the set is empty already for `i, j ≤ 0` (`q^{1+i}|x − p/q| = q^i|qx − p| ≤ |qx − p| < 1/M < c`), refuting clause (I) at `(0,0)` as well. So under both readings the conjecture as a conjunction is false. Handling of "the intersection": formalized as an arbitrary subset `I(i,j) ⊆ Bad(i,j)` (covering both the `∩_{i+j<0}` reading — proved to have dimension 0 via `dimH_iInter_badA/badB` — and `Bad(i,j)` itself), which is the strongest form available for an undefined phrase. The report also correctly notes that stricter variants (both coordinates, strict inequality, all nonzero `q`) define smaller, still-empty sets. No hypothesis is strengthened on the witness weighting; the refutation direction is airtight.

## Issues found

- Minor hygiene: one stale `conjecture.md` entry in `verification/SHA256SUMS.txt`; the file itself is correct.
- Reading A is likely not the literature's intended reading of the definition (one power of `q` off); this does not affect the verdict since reading B suffices for the conjunction, and the report is explicit about which clause falls under which reading.

## Verdict

APPROVED. A clean, machine-checked disproof built on a real two-dimensional Dirichlet theorem, decisive for the second clause under the faithful reading and for the whole conjecture under both readings, with clean build and axioms and a scrupulously scoped report.
