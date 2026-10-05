# Disproof of conjecture 00000006891

The standard complex 2×2×2 W tensor has ordinary tensor rank 3 and least closed projective secant index 2. This contradicts the first conjecture clause identifying tensor rank with the secant hierarchy index. The separate claim about general tensors and dimension counting is not needed.

`conjecture.md` is an exact copy of the official bilingual source. `main.tex` and `main.pdf` give the complete argument and explain the formalization. `lean/` contains the Lean 4.19.0 project, with Mathlib v4.19.0 and every dependency revision pinned in its manifest.

## Reproduce the formal checks

With the specified Lean toolchain available:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture6891/Core.lean
lake env lean -DwarningAsError=true Conjecture6891/Rank.lean
lake env lean -DwarningAsError=true Conjecture6891/Projective.lean
lake env lean -DwarningAsError=true Conjecture6891/Arc.lean
lake env lean -DwarningAsError=true Conjecture6891.lean
lake env lean -DwarningAsError=true Check.lean
```

The default build imports every implementation module. `Check.lean` prints all authored definitions and every theorem's type and transitive axiom dependencies. The only allowed foundational axioms in the recorded audit are `propext`, `Classical.choice`, and `Quot.sound`. All calculations supporting the mathematics are kernel-checked Lean proofs; there are no auxiliary numerical or symbolic computations supplying an unproved claim.

## Mathematical objects and source map

| File | Content |
| --- | --- |
| `Conjecture6891/Core.lean` | Actual nested tensor product of three copies of complex two-space; tensor-product basis and coordinate linear equivalence; the nonzero W tensor. |
| `Conjecture6891/Rank.lean` | Finite simple decompositions, their true minimum, zero padding and scalar invariance; exact tensor rank 3 by division-free slice elimination. |
| `Conjecture6891/Projective.lean` | Actual projective points and projective spans; homogeneous representative-independent equations; least projective algebraic closure; equivalence of the unclosed r-span locus with rank at most r. |
| `Conjecture6891/Arc.lean` | Polynomial degeneration through lines between distinct Segre points; second-secant membership; a homogeneous slice determinant excluding the first secant. |
| `Conjecture6891.lean` | Monotone secant hierarchy, actual least secant index, exact rank/index counterexample, and negation of the source's rank/index equality. |

The closure is defined by all homogeneous polynomial equations, and proved to be the least projective algebraic set containing the specified locus. It is not an arbitrary coordinate predicate. Continuity is used only to prove that every such equation vanishes at the limit. This does not assume a general equality between analytic and Zariski closure.

`secantIndex` is a total minimum: finite tensor decompositions prove every projective point lies in some secant variety. The zeroth secant is proved empty; the first is excluded by an explicit homogeneous equation. Thus no default value or untreated zero case determines the index.

The final result is `Conjecture6891.conjecture_00000006891_false`. Its predicate quantifies over all nonzero actual complex 2×2×2 tensors, a subclass on which the conjecture's unqualified first clause would have to hold. Ordinary rank is proved invariant under nonzero scaling. The construction is a classical distinction between tensor rank and border rank; no novelty claim is made.

## Report and verification records

Compile the standalone report with a standard LaTeX engine, for example `pdflatex main.tex` (run twice for references), or `tectonic main.tex`. `VERIFICATION.md` explains the actual checks. Detailed identities, build output, theorem audits, generated-declaration inventory, PDF checks, eligibility searches, and a separate semantic review are included. These are local validation records; maintainer acceptance is a separate decision.
