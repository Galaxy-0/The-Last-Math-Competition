# Disprove conjecture 00000004055: over the self-injective algebra k[x]/(x²) every syzygy period is 1, so no prime period is realized

The dual numbers A = k[ε] (ε² = 0, i.e. k[x]/(x²)) over any field k form a self-injective algebra (Baer's criterion) on which no module has syzygy period p for any prime p, in particular not 2.
- **Definitions.** Ω(M) is the kernel of a projective cover (P projective, π onto, ker π superfluous); the period is the least n ≥ 1 with Ωⁿ(M) ≅ M. Syzygies are a relation, and the result holds for every choice of covers.
- **Proof.** For projective P, εp = 0 implies p ∈ εP, and superfluous submodules lie in εP. So every syzygy is killed by ε, and if ε kills M then ker π = εP ≅ M. Hence Ωⁿ(M) ≅ M with n ≥ 1 forces Ω(M) ≅ M, and the period is 1.
- **Non-vacuity.** The simple module εA has period 1 (`simple_has_period_one`). The witness algebra is neither semisimple nor a field.
- **Scope.** Formalized for commutative finite-dimensional algebras, which the full clause implies, and for arbitrary modules. Not refuted: "for each p some algebra has a module of period p"; stable-category periods.
- **Main theorem.** `C4055.conjecture_4055_false (k : Type) [Field k] : ¬ PrimePeriodsRealized k`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 309 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4055/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004055.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C4055.conjecture_4055_false`, `C4055.no_prime_period`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000004055 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
