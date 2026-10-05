# Disproof of conjecture 00000000257

For every positive real constant `c`, the submitted Lean theorem produces a natural number `n ≥ 2` for which `h(-(n²+1)) < c log n`. The negative Pell equation gives unbounded `n` with `n²+1 = 2m²`, so the actual imaginary quadratic field is always `Q(√-2)` along this family. Its fixed finite class number cannot have the proposed uniform logarithmic lower bound.

The source defines a field class number, with no squarefree condition. The proof uses Mathlib's class number of the **full ring of integers**, not the class number of a varying order. It proves equality of the actual generated intermediate fields and does not need to compute the class number of `Q(√-2)`.

## Contents

- `conjecture.md`: exact bilingual source at repository commit `ba46ce0997cbf232fe95e5dced37ff4d32e1eb94` (SHA-256 `bd613a31cf77b10dba59141cb157ee8aeac43f2703364c63c22a639fb94bf47d`).
- `report.tex`, `report.pdf`: matching complete mathematical report, formal correspondence, and verification scope.
- `lean/`: complete Lean 4.19.0 project with Mathlib v4.19.0 and all nine dependency revisions pinned in the manifest.
- `verification/independent-verify.py`: executed inspection program; it builds a fresh project, checks all source and dependency identities, replays every module with warnings treated as errors, and inventories compiled declarations and their logical dependencies.
- `verification/frozen-sources.json`, `audit-names.json`: exact Lean/configuration identities and complete handwritten declaration inventory.
- `verification/root/`, `verification/reviewer/execution/`: separate clean execution records and output logs. Historical absolute paths identify the actual runs; use the command below for your own paths.
- `verification/reviewer/`: independent local semantic and report reviews. These are contributor-side checks, not maintainer approval.
- `verification/author/`: development provenance, recorded command history, and logs distinguishing early failures from final successful runs. References to temporary development snapshots are historical provenance, not dependencies of the final project.
- `verification/pdf-validation.json`, `pdf-build.log`: final PDF identities and rendering/build record.
- `SHA256SUMS.json`: hashes of every supplied file except the checksum manifest itself.

## Build the Lean project

With Lean 4.19.0 installed through elan, run inside `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture257.lean
lake env lean -DwarningAsError=true Audit257.lean
lake env lean -DwarningAsError=true Check.lean
```

Initial dependency and cache retrieval needs network access. Keep `lake-manifest.json`: Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The default targets build the main proof and handwritten axiom audit; the three explicit replays also include the definition/type inspection module. On a system where the native cache executable cannot load, the standard interpreted equivalent is `lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`.

The final theorem is `Conjecture257.conjecture_false : ¬ Conjecture257.Conjecture`. The stronger `counterexample_for_every_constant` covers every positive real constant. The field's exact degree two and positive imaginary generator are also proved explicitly. All 17 handwritten declarations and all 5 additional generated logical declarations were inspected; every transitive axiom set is a subset of `propext`, `Classical.choice`, and `Quot.sound`. There are no added axioms, admitted proofs, `native_decide`, unsafe/partial logical dependencies, or compiler-artifact exemptions in this candidate.

## Reproduce the complete execution audit

The optional inspector needs Python 3.11 or later and Git. First populate the pinned dependency packages and caches with the command above. From the submission folder, replace the three machine-specific paths below. The build directory must **not already exist**; the evidence directory's parent must exist. Use the actual Lean 4.19.0 toolchain `bin` directory (containing `lean` and `lake`).

```sh
python3 verification/independent-verify.py --ready \
  --source "$PWD/lean" \
  --build-dir /ABSOLUTE/NEW/AUDIT-BUILD \
  --evidence-dir /ABSOLUTE/AUDIT-EVIDENCE \
  --lean-bin /ABSOLUTE/LEAN-4.19.0/bin \
  --packages "$PWD/lean/.lake/packages" \
  --audit-names "$PWD/verification/audit-names.json" \
  --frozen-sources "$PWD/verification/frozen-sources.json"
```

Supply all paths explicitly; defaults preserve the original local execution environment. The script asserts the frozen source hashes, exact toolchain commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, all package revisions and clean tracked dependency sources before and after execution. It copies only submitted sources/configuration into a fresh output directory and links that directory to the pinned dependencies. It then checks all handwritten definitions, theorem types, and instances, enumerates every compiled declaration originating in the implementation modules, and traverses their logical dependency closures. Its generated metaprogram only inspects declarations; it is not imported by the mathematical proof.

Root and reviewer used the same fully inspected generic verification program in separate clean directories. Dependency caches were reused, while all candidate outputs were freshly built. These runs did not rebuild all of Lean or Mathlib from source. The Lean kernel, pinned compiler, and pinned library artifacts remain the ordinary toolchain trust boundary. There is **no auxiliary numerical computation** in the mathematical proof and no externally computed class number or approximate logarithm used as evidence.

## Rebuild the PDF

Compile `report.tex` with Tectonic, or another compatible LaTeX engine, for example:

```sh
tectonic --keep-logs report.tex
```

The supplied PDF was compiled from the exact supplied TeX and visually inspected on all three pages. PDF bytes may vary on recompilation because the exporter includes a creation timestamp. The local records describe successful verification, not a claim of maintainer acceptance.
