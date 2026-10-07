# Disprove conjecture 00000001729: the Campana point count of (ℙ¹, ½[0]+½[1]+½[∞]) is not c·√B/√log B

- **Reading.** "2[0]+2[1]+2[∞]" is read as multiplicity 2 at 0, 1, ∞, i.e. Δ = ½[0]+½[1]+½[∞]. Campana points on ℙ¹_ℤ: x = a/b in lowest terms, x ≠ 0, 1, with each of v_p(a), v_p(b), v_p(a−b) equal to 0 or ≥ 2 for every prime p.
- **Family.** Coprime m odd, n even give x = (m²+n²)²/(m²−n²)² with x − 1 = (2mn)²/(m²−n²)² (primitive Pythagorean triples); the filter's degenerate witness is not used.
- **Count.** Lean proves N(64K⁴) ≥ K²/2 for all K (coprime pairs via a union bound over odd d ≥ 3 and a telescoping sum), so N(B) ≫ √B.
- **Refutation.** N(B) is not O(√B/√log B); for no real c is N(B) ~ c·√B/√log B or eventually equal to it ("always"). The same holds for every height H^κ with 0 < κ ≤ 1, including the anticanonical height H^{1/2}.
- **Not refuted.** The one-sided lower-bound reading (it is implied), heights H^κ with κ > 1, and the undefined "additive-energy duality" conjunct. Context only: Browning–Van Valckenborgh, arXiv:1106.4472 (retrieved).
- **Main theorems.** `C1729.campana_count_disproof`, `C1729.campana_count_pow_disproof`, `C1729.campanaCount_lower`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 370 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1729/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001729.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1729.campana_count_disproof`, `C1729.campana_count_pow_disproof`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001729 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
