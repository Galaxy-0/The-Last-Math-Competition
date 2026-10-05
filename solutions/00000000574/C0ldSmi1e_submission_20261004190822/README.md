# Disproof of conjecture 00000000574

The ordinary Kazhdan–Lusztig polynomial of the two-copy parallel thickening of U(3,4) is `1 + 2X`. Its adjacent nonzero coefficients 1 and 2 are both positive, contradicting the explicit strictly-alternating-sign clause in both source languages. Refuting that clause disproves the conjunction without inventing the unspecified hypergeometric terms.

The proof constructs an actual Mathlib matroid, identifies its complete actual flat lattice and ranks, and derives the polynomial from the full defining recurrence on every interval. The final polynomial is chosen from a proved existence-and-uniqueness theorem on actual flats; it is not assigned the proposed answer.

## Reproduce the Lean verification

Lean 4.19.0 and Mathlib v4.19.0 are pinned, with all nine dependency revisions locked. From `lean/`, after installing the pinned toolchain and fetching the pinned dependencies:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture574/FlatDefs.lean
lake env lean -DwarningAsError=true Conjecture574/Matroid.lean
lake env lean -DwarningAsError=true Conjecture574/KLCore.lean
lake env lean -DwarningAsError=true Conjecture574/Lattice.lean
lake env lean -DwarningAsError=true Conjecture574/ActualKL.lean
lake env lean -DwarningAsError=true Conjecture574.lean
lake env lean -DwarningAsError=true Check.lean
```

`Check.lean` prints all 30 named definitions, abbreviations and the KL-family structure. It checks the types and transitive axiom dependencies of all 75 named theorems and five named instances. Only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms occur. There are no admitted proofs, custom axioms, `native_decide`, or auxiliary numerical programs. Finite enumeration is proved inside Lean by kernel-checked `decide`; the polynomial identities extend to every coefficient using proved degree bounds.

## Source map

- `Conjecture574/FlatDefs.lean`: the twelve-element flat presentation and its strict rank function.
- `Conjecture574/Matroid.lean`: actual uniform matroid from independence axioms, actual parallel pullback, ranks, closures, looplessness, two-element parallel circuits, and complete flat order isomorphisms. The generic surjective-pullback result preserves actual ranks.
- `Conjecture574/KLCore.lean`: the standard full interval recurrence, exact strict degree bound, general uniqueness on comparable intervals, unique polynomial values, and transport through an order isomorphism.
- `Conjecture574/Lattice.lean`: both Möbius recurrences, identification with Mathlib's `IncidenceAlgebra.mu`, genuine characteristic sums, and the candidate family satisfying every KL condition on every interval.
- `Conjecture574/ActualKL.lean`: transport onto the actual `Matroid.IsFlat` subtype with actual rank, actual characteristic polynomials, existence and uniqueness, the derived value `1 + 2X`, and the sign contradiction.
- `Conjecture574.lean`: imports the complete proof project.

The source paths above are relative to `lean/`. `main.tex` and `main.pdf` are the matching report; compile with `pdflatex main.tex` twice or `tectonic main.tex`. `conjecture.md` is an exact copy of the bilingual source. `VERIFICATION.md`, `SEMANTIC_REVIEW.md`, and `verification/` provide execution, identity, eligibility and internal review records.

## Interpretation and scope

The eight-element witness has one added copy per original element, or two total copies in each of four parallel classes. The formal generic rank-preserving flat correspondence explains why parallel-copy parameter conventions do not change the obstruction. No direct-sum interpretation or negative-variable substitution is introduced.

The KL definition is the standard ranked-flat interval formulation of Elias–Proudfoot–Wakefield. There is no existing global matroid KL function in this pinned Mathlib version. The submission proves the required existence and uniqueness for this actual matroid instead of postulating such a global implementation. Incomparable pairs are unconstrained and no uniqueness is claimed for them. The final sign predicate is a necessary condition for strict alternation; violating it with two positive adjacent coefficients suffices.

The independent execution uses a fresh submission build with a pinned dependency cache, not a source rebuild of all dependencies. Local validation and internal semantic review are distinct from official maintainer acceptance.
