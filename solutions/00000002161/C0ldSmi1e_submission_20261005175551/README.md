# Conjecture 00000002161: disproof by the all-positive path P4

The path `0-1-2-3` is connected and noncomplete. It has independence number 2, positive inertia index 2, and minimum orientable genus 0. Thus it attains the equality printed in the conjecture while contradicting the claimed genus 1. The proof addresses both a per-graph minimum and a minimum across the eligible class.

## Contents and scope

- `report.tex` and `report.pdf`: matching four-page mathematical report.
- `conjecture.md`: exact English and Chinese source used, unchanged.
- `lean/`: complete Lean 4 project with pinned dependency manifest; no build cache or shared-directory symlink is included.
- `auxiliary/`: independent exact Python verification, full certificate and reproducible execution evidence.
- `verification/`: frozen input hashes, independent execution logs, local semantic review, source provenance, and inspection tooling.

The signed graph, maximum independent-set cardinality, characteristic-polynomial root multiset (including multiplicity), and complete finite rotation-system certificate are checked in Lean. Genus uses the standard combinatorial definition of orientable cellular embeddings through rotation systems and the integer Euler formula. The report explains its geometric meaning with a disk-and-band construction and cites the standard correspondence. A separate general-topology realization theorem is not formalized in Lean, and no such theorem is supplied as an axiom. This boundary is explicit in the report and local semantic review.

The printed inequality is not silently corrected or assumed as a universal theorem. The counterexample satisfies its equality exactly. The complete-graph exception and even the stronger condition of connectedness are verified.

These are contributor-side verification records. They do not claim maintainer acceptance or constitute a repository review under `solutions/00000002161/review/`.

## Reproduce the Lean proof

Install the toolchain named in `lean/lean-toolchain` (Lean 4.19.0). With `lake` for that toolchain on the command path:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture2161.lean
lake env lean -DwarningAsError=true Audit2161.lean
lake env lean -DwarningAsError=true Check.lean
cd ..
```

Keep `lake-manifest.json`: it pins Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0) and all eight transitive packages. Initial dependency/cache retrieval requires network access. The verification builds used fresh project output directories and existing caches for these exact dependencies; they did not perform a full source rebuild of Mathlib. Dependency revisions and tracked-source cleanliness were checked before and after.

The principal theorems, in namespace `Conjecture2161`, are `counterexample_certificate`, `not_per_graph_genus_one`, and `not_class_minimum_one`. `Audit2161.lean` prints the axioms for all 50 handwritten declarations. `Check.lean` also prints all definitions and checks every theorem/instance type.

The entire proof project contains no admitted proof, `native_decide`, custom axiom, or authored unsafe/partial declaration. Every logical declaration has only `propext`, `Classical.choice`, and `Quot.sound` among its transitive axiom dependencies.

## Reproduce the independent computations

Python 3 with only its standard library is required:

```sh
python3 auxiliary/replay.py
```

The replay must finish successfully with `Byte-identical to first output: True` and certificate SHA-256 `f3eb8b8948075f86c1fdad48b2456a562102b48a8444a85c3a37309e8909fd27`. It writes a fresh replay log and hash record beside the checker. All 16 subsets, all 24 determinant terms, exact Sturm root counts with multiplicity, dart incidence and permutations, polygon side-gluing and vertex links, and drawing intersections are checked. Purposeful boundary cases and invalid-input tests are included. See `auxiliary/REPORT.txt` and `certificate.json` for details.

## Reproduce the expanded trust audit

Python 3.11+ is required for this optional execution inspector. After the dependencies above are installed, set the four example paths below to absolute locations on your machine; the two output directories must not already exist. `LEAN_BIN` denotes the pinned toolchain's `bin` directory.

```sh
python3 verification/independent-verify.py --ready \
  --source /ABSOLUTE/SUBMISSION/lean \
  --build-dir /ABSOLUTE/NEW/clean-project \
  --evidence-dir /ABSOLUTE/NEW/execution-evidence \
  --lean-bin /ABSOLUTE/LEAN_BIN \
  --packages /ABSOLUTE/SUBMISSION/lean/.lake/packages \
  --audit-names /ABSOLUTE/SUBMISSION/verification/audit-names.json \
  --frozen-sources /ABSOLUTE/SUBMISSION/verification/frozen-sources.json
```

The inspector covers all 207 declarations originating in the proof modules: 120 safe logical declarations (50 handwritten and 70 generated), 81 compiler-stage definitions, and six compiler-generated unsafe axiom stubs. Every logical declaration has an empty unsafe/partial/missing dependency closure. All runtime artifacts remain fully recorded, including their types and dependencies; none is admitted into a logical proof. The exact six compiler stubs are classified from the pinned compiler's eager-lambda-lifting and specialization implementations, as documented in the evidence. This inspection code uses Lean metaprogramming only to examine existing declarations; it proves no submitted theorem and is outside the mathematical Lean project.

The initial inspection stopped because it did not recognize those six compiler artifacts. The proof itself built and replayed successfully on that attempt. `verification/attempt-history.md` records the correction and retained evidence. A second independent semantic reviewer used a separate clean build and separately authored environment inspector.

## Rebuild the report

`report.tex` is standalone. For example, with Tectonic already installed:

```sh
tectonic report.tex
```

The supplied PDF was built from the supplied source and all four pages were visually inspected. Source and output hashes are recorded in `verification/pdf-verification.json`.
