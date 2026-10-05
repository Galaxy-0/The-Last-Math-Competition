# Disproof of conjecture 00000002307 (Fitting height versus derived length)

The conjecture (exact bilingual text in `conjecture.md`) claims that for solvable groups the Fitting height `h`
satisfies `h <= 2*dl - 1` (`dl` = derived length), and that the bound is attained by extremal examples of derived
length 2. Both mathematical clauses are false:

- **Key lemma.** `h(G) <= dl(G)` for every solvable group: the reversed derived series is a Fitting chain, because
  its successive quotients `G^(k) / G^(k+1)` are abelian, hence nilpotent.
- **Tightness clause fails.** A solvable group of derived length 2 has `h <= 2 < 3 = 2*2 - 1`, so no extremal
  example of derived length 2 exists. Equality `h = 2*dl - 1` forces `dl <= 1`.
- **Linear bound fails as stated.** The trivial group is finite and solvable with `h = dl = 0`, and `0 > 2*0 - 1`.
  For nontrivial groups the bound does hold, by the key lemma.

The middle clause ("controlled by layerwise projections of supersolvable towers") is not a precise statement. It is
not needed: the conjunction fails as soon as either of the other two clauses fails.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report: reading, definitions (with sources), proofs, description of the Lean files |
| `lean/` | Lean 4 project (Lean v4.33.1, Mathlib v4.33.1); proof in `lean/Conjecture2307/Basic.lean` |
| `lean/Axioms.lean` | axiom audit (`#print axioms` for the main theorems) |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002307.md` |
| `SEMANTIC_REVIEW.md` | independent semantic review of report + Lean against the conjecture |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums of all files |

## Lean

Definitions follow the standard ones (Wikipedia, "Fitting length" and "Solvable group", quoted in the report):

- `FittingChain G n`: `H 0 = ⊥ ≤ … ≤ H n = ⊤`, each normal in the next, with `Group.IsNilpotent` successive quotients;
- `fittingLength G` = least length of a Fitting chain;
- `derivedLength G` = least `n` with `derivedSeries G n = ⊥`.

Main theorem:

```lean
theorem conjecture_00000002307_false : ¬ (LinearBound ∧ TightAtDerivedLengthTwo)
```

with `not_linearBound`, `not_tightAtDerivedLengthTwo`, `fittingLength_le_derivedLength`,
`linearBound_of_nontrivial` and `derivedLength_le_one_of_tight` proved separately.

The proof contains no `sorry`, `admit`, `native_decide` or `axiom`. Every theorem depends only on `propext`,
`Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

On 2026-10-04 there was no solution folder for 00000002307 on `main` and no open pull request mentioning it. The
pull request adds only this submission folder.
