# Disprove conjecture 00000008666: non-Hamiltonian Cayley digraphs do not form a finite list

The conjecture is a conjunction of four laws. The second (finite list law) says that the exceptions, which both language versions identify as Cayley digraphs without a Hamiltonian cycle (Chinese: 无 Hamilton 的 Cayley 有向图), form a finite list.

**Key fact (Rankin's coset argument).** Let `G` be a finite abelian group and `a ≠ b` with `a b⁻¹` generating `G` and `ord a, ord b < |G|`. In a directed Hamiltonian cycle of `Cay(G, {a, b})`, if the step at `x` is `a` then so is the step at `x a b⁻¹`, by injectivity of the successor map. So all steps are equal, and the cycle closes after `ord a` or `ord b < |G|` steps, which is a contradiction.

**Infinite family.** For every odd `n ≥ 3`, `Cay(ℤ/2 × ℤ/n, {(1,0), (0,1)})` (a cyclic group of order `2n`) has no directed Hamiltonian cycle. The generating set omits the identity. The orders `2n` are unbounded, so the exceptions are infinitely many and the finite list law is false. The conjunction is therefore false whatever the other three laws mean.

**Lean.** `Conjecture8666/Basic.lean` (297 lines) defines Cayley digraphs, with a proof that their underlying simple graph is Mathlib's `SimpleGraph.mulCayley`, and directed Hamiltonian cycles as bijective cyclic enumerations. It proves `rankin`, `rankin_family`, `exceptionOrders_infinite` and the main theorem `conjecture8666_false (H P L : Prop) : ¬ (H ∧ FiniteListLaw ∧ P ∧ L)`. The axioms are `propext`, `Classical.choice` and `Quot.sound` only.

**Scope.** "Known exceptions" is refuted both literally (there are infinitely many exceptions) and epistemically: Rankin's family is classical, and the standard reference states that every cyclic group whose order is not a prime power has a non-Hamiltonian directed Cayley graph. Clause 1 read for digraphs is also refuted in Lean (`directedHamiltonianLaw_false`). The undirected Lovász-type clause is not claimed and is not needed.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8666/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008666.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture8666.conjecture8666_false`, `Conjecture8666.exceptionOrders_infinite`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000008666 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
