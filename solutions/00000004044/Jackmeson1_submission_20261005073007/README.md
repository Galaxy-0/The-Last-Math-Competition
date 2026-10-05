# Disprove conjecture 00000004044: HH^1 of the Kronecker quiver K_3 is not solvable

The conjecture claims that HH^1 = Der/Inn of a quiver algebra is solvable if and only if all oriented cycles are broken after removing at most one vertex.
**Counterexample.** The generalized Kronecker quiver K_3 has 2 vertices and 3 parallel arrows. It has no oriented cycles, so the cycle condition holds without removing any vertex. Yet over every field k, HH^1(kK_3) is not solvable.
- **Definitions.** Der, Inn and HH1 = Der / Inn are defined for any associative algebra. Der consists of the Leibniz maps; Inn consists of the inner derivations ad a and forms a Lie ideal; HH1 is Mathlib's quotient Lie algebra.
- **The algebra.** kK_3 is built on the path basis. `basis_mul_basis` proves that a product of basis paths is their concatenation or 0, and `paths_bijective` matches the basis with Mathlib's `Quiver.Path`s.
- **Non-solvability.** The derivations D_ij (alpha_j -> alpha_i) satisfy [D_im, D_mj] = D_ij and are not inner. So their classes lie in every term of the derived series, which never reaches 0.
- **Scope of validity.** No assumption on the characteristic. n = 2 lies inside the claimed n <= 6 table.
- **Lean.** The main theorem is `C4044.conjecture_00000004044_false`. Axioms: propext, Classical.choice, Quot.sound.
- **Readings.** This refutes the "solvable" reading, which is the one in the English body and the Chinese title. The Chinese body says "reducible"; the report discusses that wording but does not formalize it.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4044/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004044.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C4044.conjecture_00000004044_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004044 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
