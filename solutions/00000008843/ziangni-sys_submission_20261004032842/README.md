# Conjecture 00000008843: disproof of uniqueness

The actual closed convex real functions f(x)=0 and g(x)=1 differ, while both have inequality-defined subdifferential {0} at every real point. This refutes the unqualified unique-determination clause in both languages. The source has no normalization or additive-constant qualification. The maximal/cyclic-monotonicity clauses are not addressed.

## Contents

- report.tex and report.pdf: complete proof and formal correspondence.
- statement.md: original bilingual statement.
- lean/: Lean 4.19.0 project pinned to Mathlib v4.19.0 commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
- verification/: actual project/source checks and theorem audits.

## Reproduce

```text
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
cd ..
tectonic report.tex
```

Lean uses actual real functions, their global subgradient inequalities, Mathlib ConvexOn and genuine closed epigraphs. It proves all subgradients of every constant function are precisely zero, additive-constant invariance for all real-valued functions, equality of witness subdifferentials and inequality of the functions by evaluation. The final theorem negates the universal implication.

No auxiliary numerical computation is needed. Local ignored dependency junctions reuse the pinned cache, and no build products or caches are submitted. A fresh checkout resolves public pinned dependencies through its manifest. On Windows a short checkout path may be required; do not lake clean shared dependency junctions.
