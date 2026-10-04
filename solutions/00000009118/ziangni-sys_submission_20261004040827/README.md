# Counterexample to 00000009118

The finite-field Kakeya set consisting of the three nonzero points of (F_2)^2 has cardinality 3 < 2^2. The complete affine-line condition holds for every nonzero direction. This disproves the exact lower bound q^n stated in both source versions; it does not dispute lower bounds c_n q^n with smaller dimension-dependent constants.

`report.tex` and `report.pdf` provide the explicit three-row line table and the complete disproof. `lean/Main.lean` uses actual Mathlib `ZMod 2`, its field instance, the vector space `Fin 2 → ZMod 2`, actual vector addition and scalar multiplication, and the finite universe with zero erased. The formal Kakeya condition quantifies over all directions, base points and scalar parameters. All finite checks use kernel-checked `decide`, not native evaluation or an asserted incidence table.

The project pins Lean4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From `lean/`:

```text
lake exe cache get
lake build
lake env lean Main.lean
```

Final theorems: `FiniteKakeya9118.conjecture_00000009118` and `FiniteKakeya9118.universal_bound_false`. The separate `affinePoint_injective` theorem verifies that every nonzero-direction affine line has two distinct parameter values. All audited theorems use only standard logical axioms. No auxiliary code is needed. Compile the report with `tectonic report.tex`.
