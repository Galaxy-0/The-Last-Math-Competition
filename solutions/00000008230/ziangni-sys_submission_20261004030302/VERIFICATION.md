# Verification evidence

Date: 2026-10-04. Toolchain: Lean 4.19.0. Mathlib commit:
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Actual definitions and theorem scope

- `G` is the multiplicative form of the additive group `ZMod 3`.
- `RegularElement g` means `Nat.Coprime (orderOf g) 2`.
- `RegularClass` is a predicate on Mathlib's actual `ConjClasses G`
  quotient, requiring a regular representative.
- `IsClassFunction f` is invariance under `x*g*x^-1` for all group elements.
- `adams k f g` is `f (g^k)`.
- `fixedClassFunctions` is the complex submodule consisting of actual
  class functions satisfying the function equality `adams 2 f = f`.

`cube_one` proves every element has cube equal to the identity. Therefore
its actual order divides 3 and is coprime to 2. `ConjClasses.mkEquiv` for
commutative groups supplies the genuine group/conjugacy-class bijection.
The regular-class subtype is then proved to have cardinality 3.

`coordinates` is a complex linear equivalence from the fixed subspace to
`Complex × Complex`. It evaluates at the identity and generator. Its
explicit inverse assigns the first coordinate to the identity and the
second coordinate to both nonidentity elements. The Lean proof verifies
membership in the fixed subspace, both inverse identities, and linearity.
`fixed_dimension` obtains finrank 2 through this equivalence.

The final `counterexample` theorem states that this finrank differs from
the number of regular conjugacy classes. This directly negates a conjunct
of the original conjecture. No claims about its other conjuncts are used.

## Lean verification

Commands from the `lean` directory:

```text
lake build
lake env lean Main.lean
```

Both commands exited with code 0. The project build directory was initially
absent; dependency artifacts came from the cache matching the pinned
Mathlib revision. The full build printed `Built Main` and
`Build completed successfully.` The direct Lean check printed:

```text
'Adams8230.counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard logical axioms. No additional axioms, incomplete
proofs, `sorryAx`, or `native_decide` occur in the proof. Finite group
identities use kernel-checked `decide`; group-order, conjugacy, linear
equivalence, and dimension deductions use checked Mathlib theorems.

## PDF verification

The artifact creation marker was run before authoring. The built-in
LaTeX editor was opened and compilation attempted; its compiler returned
the known platform-directory lookup failure. Tectonic successfully
compiled the actual `report.pdf`, which has two A4 pages. Both pages were
rendered with Poppler and visually inspected in full. There was no
clipping, overlap, missing content, or overfull/underfull box warning.
Tectonic's nonfatal Fontconfig configuration diagnostic did not affect
the embedded Latin Modern fonts or the rendered output.

The proof needs no auxiliary numerical program.
