# Conjecture 00000009924: disproof

A genuine two-vertex simplicial filtration inserts its only edge at parameter zero. Its unweighted degree-zero Hodge Laplacian has eigenvalues (0,0) before insertion and (0,2) afterward. The largest eigenvalue jumps and admits no Lipschitz constant, even though vertex degrees are at most one.

## Formal scope

`Complex` is the standard abstract definition by finite vertex subsets closed downward. `filtration` has all subsets of cardinality at most one before zero and all subsets of Fin 2 afterward. The project proves downward closure, monotonicity, vertex presence and the precise insertion criterion for the edge.

The actual edge index has cardinality zero before insertion and one afterward. `boundary` is the oriented simplicial boundary; `laplacian` is boundary multiplied by its transpose, the adjoint for orthonormal simplex bases. No ghost edge or assumed matrix certificate is used. Lean evaluates the matrix, proves the complete real spectrum, exhibits the largest eigenvalue and proves it exceeds all other eigenvalues, then refutes every LipschitzWith constant for that actual top eigenvalue.

The source explicitly describes varying Hodge Laplacians. This example uses the ordinary unweighted/diagonal persistent case. A smooth weighted family would require different hypotheses. The failure of the Lipschitz conjunct suffices to disprove the full statement.

## Reproduction

Use Lean 4.19.0 and Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b, pinned by the public lakefile and manifest. Run `cd lean` and `lake build`; run `lake update` first if dependencies are absent. Ignored local `.lake` cache junctions are not part of the submission. Compile solution.tex with Tectonic or a standard LaTeX distribution. No auxiliary computation is needed.

## Validation

One final successful full lake build compiled the entire project. All eight final printed axiom audits reported exactly propext, Classical.choice, Quot.sound; no admissions, custom axioms, native decision or unsafe code occur. The only linter warnings concern redundant tactics. The two-page PDF compiled with Tectonic without layout warnings, rendered with Poppler, and both pages were visually inspected with no clipping or overlap.
