# Conjecture 00000001000: disproof of the finite-quotient clause

No finite group has a finite-piece paradoxical decomposition. Consequently no finite quotient of B(2,5) can realize Tarski number six, as the original English and Chinese statements require. This suffices to refute the conjunction; the minimum/classification clauses for infinite groups are not addressed.

The Lean project defines actual piece labels, partition fibers, left multipliers, side reassembly and separation conditions. It constructs the tagged translation map G -> G + G, derives its surjectivity and injectivity, and then proves that finite nonempty group cardinalities make the covering impossible. The final theorem covers every finite group, thus every finite quotient without any Burnside presentation assumptions.

## Contents

- report.tex and report.pdf: complete universal counting proof and formal correspondence.
- statement.md: original bilingual conjecture.
- lean/: Lean 4.19.0 project pinned to Mathlib v4.19.0, commit c44e0c8ee63ca166450922a373c7409c5d26b00b.
- verification/: actual build results and final theorem axiom audits.

## Reproduce

```text
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
cd ..
tectonic report.tex
```

No auxiliary numerical computation is needed. Local ignored dependency junctions reuse the pinned cache and are not submitted. A fresh checkout uses the public dependency manifest. On Windows, a short checkout path may be needed for dependency path limits; do not run lake clean on shared dependency junctions.

The model allows empty piece labels, which only enlarges the class of possible decompositions; excluding it also excludes the usual version in which all pieces are nonempty. The cover and separation conditions refer to actual left multiplication of group elements, not arbitrary asserted cardinality data.
