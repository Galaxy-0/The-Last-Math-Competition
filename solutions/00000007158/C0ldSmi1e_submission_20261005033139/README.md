# Disproof of conjecture 00000007158

The real matrix N = [[0, 2], [0, 0]] has complex spectrum {0}, so its actual
imaginary spectral bandwidth is zero. Its antisymmetric part is the
quarter-turn J = [[0, 1], [-1, 0]], with Euclidean operator norm one.
This refutes the explicit bandwidth-equals-norm assertion and therefore
its conjunction with any additional minimization assertion.

The report explains the literal equality reading and distinguishes it from
a containing-strip inequality. The unspecified minimization problem is not
assigned invented constraints. Radius, positive-factor, unhalved-part,
complex-adjoint, and arbitrary zero-separating norm conventions are addressed.

## Reproduce the formal proof

Use the pinned Lean 4.19.0 toolchain and Mathlib v4.19.0 manifest in `lean/`.
From that directory, with the dependencies available:

```sh
lake build
lake env lean -DwarningAsError=true Conjecture7158.lean
lake env lean -DwarningAsError=true Check.lean
```

The default Lake target is explicitly `Conjecture7158`. It includes the full
proof source. Check prints all eight definitions and the types and axiom
dependencies of all 24 authored theorems. The matrix norm uses the explicit
`Matrix.L2OpNorm` scope and is bridged to a Euclidean continuous linear map.
The spectrum is Mathlib's actual algebraic spectrum, with a proved
nonzero-eigenvector equivalence. Supremum and infimum agree with the ordinary
imaginary extrema for the proved singleton spectrum.

No external mathematical computation is needed: the determinant, spectrum,
matrix products, and norms are all proved symbolically in Lean. No admitted
proofs, `native_decide`, custom axioms, authored unsafe code, or partial
definitions are used. The three explicit noncomputable data definitions
avoid irrelevant compiler runtime artifacts; their mathematical bodies are
unchanged.

## Materials and verification

`main.tex` and `main.pdf` contain the complete report. `conjecture.md` is the
byte-identical bilingual statement. `verification.txt` summarizes the fresh
build, strict replays, full compiled-module inventory, dependency pins,
PDF inspection and eligibility audit. Detailed records and inspection scripts
are in `verification/`; their absolute scratch paths record the actual local
execution environment and are not required by the mathematical project.
`SEMANTIC_REVIEW.md` records the independent internal review of the frozen
inputs. `verification/SHA256SUMS.json` covers every other submitted file.

These are local verification records. Maintainer acceptance is separate.
