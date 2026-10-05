# Disprove conjecture 00000000502: reg I(K2)^t = 2t, so a(K2) = 2, not 1 (general formula) or 0 (chordal formula)

The conjecture defines a(G) as the slope of t -> reg I(G)^t. It claims a(G) = max{nu(G)-1, ceil((m(G)+1)/3)} for bipartite G, and a(G) = nu(G)-1 for chordal bipartite G.

**Counterexample.** Take G = K2. It is bipartite, and chordal bipartite because it has no cycles; nu = m = 1. I(K2)^t = ((x0 x1)^t) is a nonzero principal ideal of a domain, so 0 -> S(-2t) -> I^t -> 0 is its minimal graded free resolution and reg I(K2)^t = 2t. The slope is therefore a(K2) = 2. The two formulas give max{0,1} = 1 and nu-1 = 0.

**Lean.** Regularity is defined from scratch as the least r with b_j - j <= r over a minimal graded free resolution. Resolutions are encoded as matrices of homogeneous polynomials, with exactness required at every step. The equality reg I(K2)^t = 2t is proved in both directions: the upper bound comes from an explicit minimal resolution, and the lower bound holds for every resolution. Matchings use Mathlib's Subgraph.IsMatching and IsInduced, and bipartiteness uses Mathlib's IsBipartite.

**Main theorem.** `C502.conjecture_00000000502_false (k) [Field k] : ¬ GeneralFormula k ∧ ¬ ChordalFormula k ∧ ¬ Conjecture k`. It uses only the axioms propext, Classical.choice and Quot.sound.

**Scope.** This uses the literal (slope) reading. Under the constant-term reading the general formula still fails (b = 0 != 1, `constant_term_reading_false`), but the chordal clause would hold for K2.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture502/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000502.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C502.conjecture_00000000502_false`, `C502.constant_term_reading_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000502 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
