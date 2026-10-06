# Disproof of conjecture 00000005754

The final clause claims that every continuous valuation has value group a power of the integers. The Hahn-series field `HahnSeries ℚ ℚ`, with its usual lowest-exponent valuation and canonical valuation topology, has intrinsic value group `(ℚ,+)`. No Cartesian power of `ℤ` is isomorphic to this group: a nonempty power has an element with a coordinate equal to 1 that cannot be halved, while `ℚ` is divisible; an empty power is trivial.

The proof identifies the actual image on nonzero field elements, rather than merely choosing a large codomain. It proves continuity both for Mathlib's `WithZeroTopology` and for the ordinary order topology on the extended value group. The obstruction covers every index type, so no rank assignment is assumed. This negates a necessary clause shared by the exact English and Chinese originals in `ORIGINAL.md`; it does not separately settle the unspecified conversion or rank-jump clauses.

## Contents

- `lean/Counterexample.lean`: the complete mathematical proof.
- `lean/Inspect.lean`: theorem types, key axiom dependencies, and standard field/topology instances.
- `lean/SemanticChecks.lean`: independently written checks fixing the exact domain and codomain topologies and valuation definitions.
- `lean/Audit.lean`: all compiled declarations owned by the mathematical module, including generated declarations, their types, direct constants, and transitive axiom dependencies.
- `report.tex` and `report.pdf`: matching complete explanation.
- `verify.py` and `test_verify.py`: portable fresh-project verification and negative controls.
- `VERIFICATION.md` and `verification/`: recorded commands, outputs, identities, local semantic review, and PDF inspection.

## Reproduce

Use Lean 4.19.0 and the committed dependency manifest (Mathlib v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`). Initialize the pinned standard packages and their cache from this submission's `lean` directory:

```sh
cd lean
lake exe cache get
lake build
cd ..
python3 verify.py --dependency-root lean/.lake/packages
python3 test_verify.py --compiled-controls --dependency-root lean/.lake/packages
```

Python 3 uses only the standard library. The scripts print the new temporary output directories containing actual commands and results. If `lake` is not on PATH, supply `--lake /path/to/lean-4.19.0/bin/lake`. The verifier requires the nine Git dependency checkouts at their pinned revisions with no tracked source changes; it does not download or update dependencies. Standard dependency caches may be reused, but the authored project is always rebuilt in a new directory. No auxiliary mathematical computation is needed.

For direct inspection, run from `lean`:

```sh
lake env lean -DwarningAsError=true Counterexample.lean
lake env lean -DwarningAsError=true Inspect.lean
lake env lean -DwarningAsError=true SemanticChecks.lean
mkdir -p logs
lake env lean -DwarningAsError=true Audit.lean
```

The PDF was compiled from `report.tex` and every page visually checked. It can be rebuilt with a standard LaTeX installation or Tectonic. The source also compiles in the Codex built-in LaTeX editor.

All validation and the included semantic review are local contributor checks. Repository maintainers determine acceptance.
