# Disproof of conjecture 00000000407

The table in both source languages has all three partitions of the same size n.
The actual LR-tableau definition forces |nu| = |lambda| + |mu|, so every entry
vanishes for n > 0. Thus its nonzero-entry count cannot have the claimed
positive-constant asymptotic. The empty case is checked separately: A(0) = 1.

This addresses the literal displayed indexing. It does not assert a solution
to a different problem obtained by repairing the indexing or supplying an
undefined configuration family. The full source is in `conjecture.md`, and
`report.tex` / `report.pdf` give the proof and the formal correspondence.

## Reproduce

Use Lean 4.19.0 with the committed manifest (Mathlib v4.19.0 and nine exact
dependency revisions). With that toolchain and Python 3 available:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture407.lean
lake env lean -DwarningAsError=true Audit407.lean
lake env lean -DwarningAsError=true Check.lean
cd ..
python3 auxiliary/verify.py > actual-output.json
cmp actual-output.json auxiliary/expected-output.json
```

The auxiliary program uses only Python's standard library. It enumerates
116,947 ordered source triples through n=10 and compares 4,170 coefficients
against a separate exact polynomial implementation. Positive coefficients,
degree-compatible zeros, multiplicity two, and isolated failures of each
tableau condition are tested. These finite computations check definitions;
the universal result is the Lean proof and does not depend on Python.

Compile the standalone report with XeLaTeX or Tectonic. The submitted PDF was
compiled from the exact submitted TeX and all five pages were visually checked.

## Verification evidence

- `verification/independent-review/`: full nonauthor semantic review and exact
  source identities, including the final formatting-only report binding.
- `verification/root-execution/` and `verification/reviewer-execution/`: two
  fresh project builds, complete strict replay records and command outputs,
  compiled environment inventories, every declaration's type and axioms.
- `verification/tools/`: executable audit tooling and frozen source/inventory
  inputs. Its metaprogramming inspects compiled objects; it proves no theorem.
- `verification/author/`: authorship provenance and final author checks.
- `verification/source-scope/`: source-only interpretation assessment, with the
  original deferral retained and its narrower disproof-only resolution.
- `verification/eligibility/`: dated public prior-solution audit summary. This
  is a non-atomic snapshot, not a claim about inaccessible material or the future.
- `verification/pdf/` and `verification/auxiliary-root-replay.json`: export,
  visual inspection, and independently reproduced auxiliary output records.

The audit covers 42 authored declarations (26 theorems, three named instances,
13 definitions/structures/abbreviations) and all 78 compiled declarations,
including generated ones. Only subsets of the standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound` occur. No admitted proof,
`native_decide`, custom axiom, unsafe/partial proof dependency, or skipped
kernel check is used.

For the full executable audit, use Python 3.11+ and explicitly supply local paths
to the unchanged tool. BUILD_DIR must not exist; EVIDENCE_DIR is a fresh output
directory; LEAN_BIN contains Lean 4.19.0; PACKAGES contains the nine pinned,
clean dependency checkouts and their available build artifacts:

```sh
python3 verification/tools/independent-verify.py --ready \
  --source lean --build-dir "$BUILD_DIR" --evidence-dir "$EVIDENCE_DIR" \
  --lean-bin "$LEAN_BIN" --packages "$PACKAGES" \
  --audit-names verification/tools/audit-names.json \
  --frozen-sources verification/tools/frozen-sources.json
```

Recorded absolute paths describe the original executions; they are not required
installation locations. Both independent executions rebuilt the submitted
project, reusing pinned dependency caches. They did not rebuild Lean itself or
all of Mathlib from source. No formal equivalence to a separate Schur-function
library is claimed: the semantic bridge is the conventional LR-tableau
definition, inspected against primary references in the report and review.

The mathematical author began from the exact source in a fresh context; a
tool call incidentally exposed older agents' status summaries but no old proof
files or strategies were used. The independent mathematical reviewer began
separately, read the whole report and project, and repeated the computations.
Development compile failures were corrected before the final freeze. Scratch
proof attempts are not submitted as verified evidence. All claimed successful
checks refer to the final frozen sources identified in the included records.

These records establish local validation, not maintainer acceptance. Changes
are confined to this personal submission directory. `SHA256SUMS.json` covers
every submitted file except itself.
