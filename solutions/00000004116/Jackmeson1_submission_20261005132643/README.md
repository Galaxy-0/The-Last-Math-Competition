# Disprove conjecture 00000004116: asdim Conf_1(ℝ) = 1, not dn − 1 = 0

- **Objects.** The ordered configuration space Conf_n(ℝ^d) (injective configurations, Euclidean metric of (ℝ^d)^n) and Gromov's asymptotic dimension as defined on Wikipedia (retrieved, quote-checked).
- **Lower bound.** A chain argument proves asdim Conf_n(ℝ^d) ≥ 1 for all n, d ≥ 1 (`one_le_asdim_conf`).
- **Upper bound.** An interval cover of length 3R proves asdim Conf_1(ℝ) ≤ 1, so asdim Conf_1(ℝ) = 1 exactly (`asdim_conf_one_one`).
- **Conclusion.** The formula asdim = dn − 1 fails at n = d = 1 (`conjecture_4116_false`).
- **Scope.** The general failure (asdim = dn for all n, d) is argued in prose only; if the claim is meant only for n ≥ 2 the Lean does not refute it. Undefined terms ("coarse dimension", "fractal correction") are not addressed.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 208 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** orionsheep submitted this conjecture in PR #294, which was closed without merging. The reviewer's reason: "The main theorem is (1*1−1 = 0 ∧ 1 ≠ 0) ∧ (1*2−1 = 1 ∧ 2 ≠ 1) ∧ 0 < 1 ∧ 1 < 2; no Conf_n(R^d), no asymptotic or coarse dimension — the off-by-one refutation is asserted only in prose". This submission defines the ordered configuration space Conf_n(ℝ^d) in Lean, with the Euclidean metric of (ℝ^d)^n. It also defines Gromov's asymptotic dimension as on Wikipedia: for every R ≥ 1, a uniformly bounded cover in which every closed R-ball meets at most n+1 members. It proves asdim Conf_n(ℝ^d) ≥ 1 for all n, d ≥ 1 by a chain argument, and asdim Conf_1(ℝ) = 1 with both bounds. From these it derives that the formula asdim Conf_n(ℝ^d) = dn − 1 fails at n = d = 1.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4116/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004116.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C4116.conjecture_4116_false`, `C4116.asdim_conf_one_one`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004116 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
