# Disprove conjecture 00000002416: no open subgroup of Gal(Q̄/Q) is finitely generated, so the generator spectrum is not {2,3}

The conjecture's first clause says the minimal numbers of generators of open subgroups of G_Q = Gal(Q̄/Q) form the set {2, 3}.
- **Result.** No open subgroup of G_Q is topologically finitely generated, so every open subgroup has d = ∞ and the spectrum is {∞} (`genSpectrum_absGal`). The same holds for abstract generation.
- **Quadratic characters.** For each prime p, χ_p(σ) = σ(√p)/√p is a homomorphism G_Q → {±1} with an open kernel. If χ_p = χ_q, then √p·√q is fixed by G_Q and so is rational, which forces p = q.
- **Counting.** A homomorphism with an open kernel is determined by its values on a topological generating set, so a finite generating set would admit only finitely many χ_p.
- **Open subgroups.** G_Q is compact, so a finite generating set of an open subgroup, plus finitely many coset representatives, would generate G_Q.
- **Setting.** Mathlib's `Field.absoluteGaloisGroup ℚ` with the Krull topology; open subgroups carry the subspace topology.
- **Main theorems.** `C2416.conjecture_2416_false`, `C2416.genSpectrum_absGal`, `C2416.conjecture_2416_false_abstract`.
- **Scope.** Only the first of the three semicolon-separated clauses is refuted; the second presupposes it. Readings where "G_Q" means a local, restricted-ramification or pro-p group are not addressed.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 296 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2416/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002416.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2416.conjecture_2416_false`, `C2416.genSpectrum_absGal`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002416 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
