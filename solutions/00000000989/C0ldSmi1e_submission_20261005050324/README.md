# Disproof of conjecture 00000000989

Under the standard positive-map meaning of indecomposable, every completely
positive map is decomposable: take the completely positive summands S = Phi
and T = 0 in Phi = S + transpose composed with T. Thus no completely positive
map is indecomposable, at any Choi rank, and no requested nonempty family exists.

The report discloses the square-system convention M_d(C) -> M_d(C), with d a
positive matrix side length. It distinguishes positive-map indecomposability
from extreme rays, extreme points and direct-sum indecomposability. Zero
summands are allowed in the standard definition; no trace-preserving or unital
normalization is imposed. The source's parenthetical "extremal Choi rank"
provides no optimization class; its actual numerical equality is retained.

## Reproduce

Use the pinned Lean 4.19.0 toolchain and Mathlib v4.19.0 manifest in `lean/`.
From that directory, with the dependencies available:

```sh
lake build
lake env lean -DwarningAsError=true Conjecture989.lean
lake env lean -DwarningAsError=true Check.lean
```

The explicit default target is `Conjecture989`. The source uses actual complex
matrices and complex-linear maps. It proves the PSD quadratic-form bridge,
ampliation Kronecker action and block expansion, actual transpose/map identities,
the Choi sum formula, complex image-dimension rank, and the positive-dimensional
corank-one interpretation of d squared minus one. The final theorem is
`Conjecture989.conjecture989_false`; `no_nonempty_family` is universe-polymorphic
and even permits dimensions varying with the index.

`Check.lean` prints all 13 definitions/abbreviations and the types and axiom
dependencies of all 22 authored theorems. No numerical or external mathematical
computation is needed. There are no admitted proofs, `native_decide`, custom
axioms, unsafe source declarations or partial definitions.

## Materials

`main.tex` and `main.pdf` contain the complete mathematical report. `conjecture.md`
is the byte-identical bilingual source. `verification.txt` summarizes the fresh
build, strict replays, exhaustive compiled-module inventory, dependency pins,
PDF checks and eligibility audit. `verification/formal-correspondence.txt`
explains the definitions and theorem correspondence in detail. Other records
and inspection scripts are in `verification/`; their absolute scratch paths
document the local execution and are not needed by the mathematical project.
`SEMANTIC_REVIEW.md` records the independent internal review of frozen inputs.
`verification/SHA256SUMS.json` covers every other submitted file.

Local validation and internal review do not establish maintainer acceptance.
