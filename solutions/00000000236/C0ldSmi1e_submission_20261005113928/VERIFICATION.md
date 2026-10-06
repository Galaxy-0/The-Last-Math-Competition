# Verification

The coordinator and a separate nonauthor reviewer each rebuilt the final frozen proof in a fresh directory and replayed every project Lean source with warnings treated as errors. The exhaustive compiled-module inventory covers all 50 declarations: 33 written declarations (11 definitions, 22 theorems, no custom instances) and 17 generated equation/proof declarations. All actual types, axiom sets and transitive logical type/body dependencies, including inductive/recursor dependencies, were checked. The explicit inspection also prints the definition bodies and resolved standard instances.

Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms. There are no admitted proofs, custom axioms, `native_decide`, unsafe or partial logical dependencies. The final compiled module also has no unnecessary runtime compiler constants. No numerical computation supplies any hypothesis or conclusion: the analytic and parity arguments are entirely kernel-checked in Lean.

Lean is 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. The actual compiler binary SHA-256 was `5c1fe58db7d10b1cd0ddff1a1cbc49db2396fff9c6c983cc3b49f1c5c1ae241b` on arm64 macOS. Mathlib is v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine exact dependencies are pinned in `lean/lake-manifest.json`; actual revisions and tracked-source cleanliness were checked before and after fresh verification. Cached dependency build artifacts were reused. We do not claim to have rebuilt the compiler or all Mathlib from source.

## Reproduce the proof

With the pinned Lean toolchain installed, run from `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture236.lean
lake env lean -DwarningAsError=true Check.lean
```

Keep all manifest revisions fixed. `Check.lean` only prints definitions, theorem types and axiom dependencies; it supplies no mathematical theorem.

## Reproduce the complete trust audit

From the submission directory, with Python 3.11 or later and Git available, replace the tool path below with your pinned toolchain directory. The build directory must not already exist.

```sh
python3 verification/independent-verify.py --ready \
  --source "$PWD/lean" \
  --build-dir /tmp/tlmc236-fresh-build \
  --evidence-dir /tmp/tlmc236-fresh-evidence \
  --lean-bin '<directory containing pinned lean and lake>' \
  --packages "$PWD/lean/.lake/packages" \
  --audit-names "$PWD/verification/audit-names.json" \
  --frozen-sources "$PWD/verification/frozen-sources.json"
```

The verifier checks source/configuration identities, compiler commit and all actual dependency revisions, builds and replays the project, and inventories every compiled constant by its originating module. The generated `IndependentEnvironmentInventory.lean` is read-only inspection metaprogramming, outside the proof's imports.

## Replay the explicit declaration and instance inspection

After the fresh build above:

```sh
python3 verification/replay-author-inspection.py \
  --project /tmp/tlmc236-fresh-build \
  --auxiliary "$PWD/verification/author" \
  --output /tmp/tlmc236-inspection-replay \
  --lean-bin '<directory containing pinned lean and lake>'
```

The output directory must be new. This executes the included `Inspect.lean` and `Audit.lean` with warnings as errors. They print all 33 written declaration types/axioms, definition bodies and standard instances, and check their full logical closure. Both tools were actually replayed against the final source. The current complete-module audit additionally covers every generated declaration without a namespace-prefix assumption.

## Development history and scope

`author-history.json` preserves the author's text files, source snapshots, execution records, complete captured logs and helper source as historical data. The 30 completed execution records are checked against their recorded log hashes. This archive is not a set of current reproduction commands: its absolute paths and source hashes belong to past attempts. In particular, the historical final-input checker assumes that `Check.lean` is absent and must not be used as a validator for this final package.

The first broad-import development build was interrupted; its child stdout and exact timestamps were not recovered by the original recorder. The observed session exit was 130. A process-list diagnostic also failed to launch. These limitations are explicitly preserved in the author notes; neither attempt is counted as successful validation. Later recorded builds and the final independent executions have complete outputs.

The author's original completed source had SHA-256 `b159312a5ff44597b1005591400c5dc93a12c56fbee777c5c93da2e70ffed13f`. The coordinator added only `noncomputable` to `integerMatrix`, `realMatrix` and `gram`, leaving all mathematical bodies, statements and proofs unchanged. This suppresses unnecessary executable specializations. Two intermediate exhaustive gates rejected compiler-only artifacts even though source compilation and every logical closure passed; their results remain in `coordinator-attempts.json`. The unchanged conservative verifier then passed on the final source, SHA-256 `3f92cd7332f94f86d3e31efb9653bdd7c30201dba43e1d3110066c907ac8e781`. Author notes describe their original hash; final coordinator and reviewer records bind the actual submitted hash.

## Report, eligibility and file integrity

The final TeX compiled successfully in the native editor and exported with Tectonic without warnings or box diagnostics. All four rendered pages and the entire extracted text were inspected. `verification/export-pdf.py` can reproduce export/rendering with explicit `--report`, `--evidence`, `--tectonic` and `--poppler-dir` arguments. Use a separate directory containing a copy of `main.tex` to preserve submitted bytes. Omit `--native-confirmation` for your own export: the script cannot invoke the native editor or perform visual inspection, and correctly leaves new output awaiting review.

The candidate-specific public-history audit found no prior same-problem submission or invalid attempt requiring an error account. Final delta checks compare the main commit, complete PR/issue catalogs, public refs and mutable discussion/review inputs with that audit and inspect any change. Both complete dated contribution guides and the exact source are included. Public observations are timestamped and cannot certify deleted, private or inaccessible material.

The separate nonauthor review binds the frozen review-input manifest. `verification/SHA256SUMS.json` binds every other submitted file. These records establish local validation, not maintainer acceptance.
