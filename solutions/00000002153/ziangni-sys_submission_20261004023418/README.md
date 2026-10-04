# Conjecture 00000002153: disproof of the high-girth clause

The star K1,9 has the Fiedler vector (0,1,1,1,1,1,1,1,1,-8). Its nine strong nodal domains exceed 2sqrt(10). The first multiplicity clause is not refuted. Nodal domains follow the statement's sign-constant convention: components of the positive and negative induced graphs. The distinct weak convention permits zero vertices and gives 2 here; the report states this explicitly.

## Files

- report.tex / report.pdf: complete argument and semantic scope.
- lean/Main.lean: actual finite adjacency, D-A Laplacian over real numbers and coordinate equality, all-real spectrum restriction, constant zero kernel, Fiedler property, no short cycles, sign-path correspondence, exact 9-domain representatives and universal-bound negation.
- verify.py: independently computed exact rational eigenbasis, full rank check, exhaustive embedded 3/4-cycle check, and graph-component traversal.
- verification/: reproduction results.

## Reproduce

Lean 4.19.0, Mathlib v4.19.0 commit c44e0c8ee63ca166450922a373c7409c5d26b00b. The manifest pins all dependency revisions.

```text
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
cd ..
python verify.py
tectonic report.tex
```

On Windows, use a short project path (e.g. subst of the worktree) and ensure the Lean 4.19.0 bin directory precedes other Lean versions on PATH. Local dependency junctions and build products are ignored and not submitted. This checkout reused the pinned cached dependencies; a clean checkout can fetch them via the manifest. To clean only this project's products, remove only lean/.lake/build; avoid lake clean when local dependencies share a cache.

The final theorem uses only standard logical axioms propext, Classical.choice and Quot.sound. There are no omitted proofs, custom axioms or native decision shortcuts. All nine sign components are formalized, not asserted as input.
