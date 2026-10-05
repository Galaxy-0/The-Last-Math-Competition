# Disprove conjecture 00000001046: x + x^(q−2) has differential uniformity ≥ 4 whenever 3 | q − 1

- **General theorem.** Over any finite field F_q with 3 | q − 1, take ω of order 3 in F_q^×. Then f(x+1) − f(x) = 2 for f(x) = x + x^(q−2) has the four distinct solutions 0, −1, ω, ω², so δ(f) ≥ 4 (`four_le_diffUniformity`).
- **Consequences.** This holds for q = 4^k (every even m in q = 2^m) and q = 7^k for all k ≥ 1, so "δ = 2 for large q" fails over all prime powers, over q = 2^m and over odd q (`not_eventually_two`, `not_eventually_two_char_two`, `not_eventually_two_odd`, using Mathlib's `GaloisField`).
- **Definitions.** The map and the differential uniformity (maximum over a ≠ 0 and all b of the number of solutions) are defined for an arbitrary finite field.
- **Not refuted.** A reading restricted to m odd, or to q = 3^k.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 221 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** A submission by orionsheep for this conjecture (PR #157) was closed without merging. The reviewer's reason: "the Lean verifies only three finite instances (q = 16, 256, 1024, each with count = 4, i.e. δ = 4). Three data points are consistent with δ = 2 for all q > 1024, so the asymptotic claim is untouched", and asked for "a version proving the general even-m case in Lean". This submission defines the map x ↦ x + x^(q-2) and differential uniformity over an arbitrary finite field in Lean. It proves δ ≥ 4 whenever 3 ∣ q − 1, using a cube root of unity from Cauchy's theorem in Fˣ. It applies this to GaloisField 2 (2k) and GaloisField 7 k for every k ≥ 1, and proves directly that there is no N with δ = 2 for all q > N, both over all finite fields, over q = 2^m and over odd q.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1046/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001046.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1046.four_le_diffUniformity`, `C1046.not_eventually_two`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001046 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
