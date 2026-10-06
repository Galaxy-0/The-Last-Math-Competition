# Verification

The exact proof was rebuilt in fresh independent projects by the coordinator and a separate nonauthor reviewer. Both sources were replayed with warnings as errors. All 29 authored declarations (8 definitions, 21 theorems, no instances) and all 9 generated constants were inventoried by actual module origin. Types, definitions, standard instances, axiom sets and transitive logical dependency safety were checked. The only axioms found were `propext`, `Classical.choice` and `Quot.sound`; there are no admitted proofs, custom axioms, `native_decide`, unsafe or partial logical dependencies.

Lean is 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. Mathlib is v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine package revisions are pinned in `lean/lake-manifest.json` and were checked with tracked sources clean before and after verification. Standard cached dependency artifacts were reused; these checks do not claim a from-source rebuild of all Mathlib or the compiler.

## Reproduce the proof

With the pinned Lean toolchain available, from `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture7668.lean
lake env lean -DwarningAsError=true Check.lean
lake env lean -DwarningAsError=true ../verification/author/Inspect.lean
```

Lake must fetch the exact packages from the included manifest. Do not update dependency revisions. `Check.lean` and `Inspect.lean` only print existing declarations and axiom dependencies; they prove no submitted theorem.

## Reproduce the complete environment audit

From the submission directory, replace the angle-bracket paths with local absolute paths. The build directory must not already exist. Python 3.11 or later, Git, Lean and Lake are required.

```sh
python3 verification/independent-verify.py --ready \
  --source "$PWD/lean" \
  --build-dir /tmp/tlmc7668-fresh-build \
  --evidence-dir /tmp/tlmc7668-fresh-evidence \
  --lean-bin '<directory containing pinned lean and lake>' \
  --packages "$PWD/lean/.lake/packages" \
  --audit-names "$PWD/verification/audit-names.json" \
  --frozen-sources "$PWD/verification/frozen-sources.json"
```

This verifier requires the frozen file hashes, checks compiler/package identities and clean tracked dependencies, rebuilds, directly replays all source, and inventories every constant originating in the proof module. Its generated `environment-inventory.lean` is inspection metaprogramming, kept outside the proof's imports. The inventory includes generated constants and flags unsafe, partial or missing transitive logical dependencies.

## Additional author-style inspection

The coordinator made only path/CLI changes to the author's original checker, preserving its historical execution records. To rerun the portable version, use the clean `lean/` project, not the inventory-enriched temporary build. The output directory must be new.

```sh
python3 verification/author_check.py \
  --project "$PWD/lean" \
  --output-dir /tmp/tlmc7668-author-style-check \
  --lean-bin '<directory containing pinned lean and lake>' \
  --eligibility-dir "$PWD/verification/inputs" \
  --preassessment "$PWD/verification/semantic-preassessment.txt"
```

The portable checker was independently executed by coordinator and reviewer: all 32 commands passed and its generated `Inspect.lean` exactly matches the author's original. It prints fully explicit types, relevant standard-library definitions and all authored axiom dependencies. The original checker source is preserved as historical text; its absolute paths describe the original run. Each command's original stdout and SHA256 are retained in `author-command-outputs.json`; the portable replay has the analogous `auxiliary-command-outputs.json`. Original JSON command records retain their actual historical paths, which are not required to exist for reproduction.

One coordinator attempt pointed this lexical checker at a temporary project containing the environment inspection harness. It correctly rejected an inspection-only `axiom` token before any build. The corrected invocation used the clean proof project and passed. An initial author inspection used an unsupported print-width option; the final inspected file uses the supported option and passed. Neither event changed the proof. The provenance record retains these setup failures.

## Report and eligibility

The native editor compiled the final TeX successfully. An independent Tectonic export had no warnings or box diagnostics. Both pages were rendered, their complete text compared, and every page visually inspected. `verification/export-pdf.py` reproduces export/rendering with explicit `--report`, `--evidence`, `--tectonic` and `--poppler-dir` paths. Omit `--native-confirmation` when independently exporting; the script cannot invoke the native editor or certify visual review. It deliberately leaves new exports awaiting visual review. To preserve the submitted PDF bytes, run it on a copy of `main.tex` in a separate report directory.

Initial and prepublication public-history audits found no prior same-problem submission or invalid attempt requiring an error account. Both complete contribution guides are included as dated inputs. A final publication delta record checks for changes immediately before submission. These timestamped public checks cannot certify deleted, private or inaccessible material.

`verification/SHA256SUMS.json` binds every other submitted file. The independent semantic review binds the complete frozen input manifest. These records establish local validation, not maintainer acceptance. No external mathematical computation was used; all auxiliary code is reproducibility, inspection, or report tooling.
