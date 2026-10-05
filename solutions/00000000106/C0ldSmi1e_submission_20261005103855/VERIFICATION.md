# Verification

The coordinator rebuilt the frozen proof in a fresh project, replayed every submitted Lean source with warnings treated as errors, and audited all 9 authored declarations (3 definitions, 6 theorems, no custom instances) and all 17 generated declarations. The complete module-origin inventory contains 26 constants. Every type, axiom set and transitive logical dependency closure was checked; the additional author inspection prints fully explicit definition bodies and the standard instances used by the statement.

Only `propext`, `Classical.choice` and `Quot.sound` occur as axiom dependencies. There are no admitted proofs, custom axioms, `native_decide`, unsafe or partial logical dependencies. The separate nonauthor review is recorded in `SEMANTIC_REVIEW.json`, including its own execution evidence and input hashes.

Lean is 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. Mathlib is v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine dependency revisions are pinned in `lean/lake-manifest.json`. Their actual revisions and tracked-source cleanliness were checked before and after the fresh verification. Cached dependency build artifacts were reused; no claim is made that all Mathlib or the compiler was rebuilt from source.

## Reproduce the proof

With the pinned Lean toolchain installed, from `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture106.lean
lake env lean -DwarningAsError=true Check.lean
```

Lake must fetch the exact dependencies in the included manifest; do not update their revisions. The proof is in `Conjecture106.lean`. `Check.lean` prints definitions, theorem types and axiom dependencies and contributes no mathematical theorem.

## Reproduce the complete trust audit

From the submission directory, with Python 3.11 or later and Git available, replace the tool path below with a local absolute path. The build directory must not already exist.

```sh
python3 verification/independent-verify.py --ready \
  --source "$PWD/lean" \
  --build-dir /tmp/tlmc106-fresh-build \
  --evidence-dir /tmp/tlmc106-fresh-evidence \
  --lean-bin '<directory containing pinned lean and lake>' \
  --packages "$PWD/lean/.lake/packages" \
  --audit-names "$PWD/verification/audit-names.json" \
  --frozen-sources "$PWD/verification/frozen-sources.json"
```

The verifier checks exact source/configuration hashes, compiler identity and all dependency revisions, builds the project, replays every source, and inventories every compiled constant originating in the proof module. It traverses logical types and bodies, including inductive/recursor dependencies. Its generated `IndependentEnvironmentInventory.lean` is inspection metaprogramming outside the proof's imports, and is not part of the mathematical argument.

## Replay the author's declaration and notation inspection

After the fresh build above, run:

```sh
python3 verification/replay-author-inspection.py \
  --project /tmp/tlmc106-fresh-build \
  --inspection "$PWD/verification/author/Inspect.lean" \
  --output /tmp/tlmc106-inspection-replay \
  --lean-bin '<directory containing pinned lean and lake>'
```

The output directory must be new. This executes the exact final `Inspect.lean` with warnings as errors, checks all 26 printed axiom sets and all three safe definitions, and saves complete output and input hashes. The coordinator's actual replay is supplied in `auxiliary-replay.json` and `auxiliary-inspection.txt`.

The original author's execution helpers are preserved as historical `.py.txt` source. They were actually executed with the historical absolute paths shown in their records; they are not portable entry points. All 19 logged command records and their complete original stdout, including developmental failures, are consolidated in `author-command-records.json` and `author-command-outputs.json`. `formal-correspondence.txt` explains every failure and its correction. These failures precede the successful final frozen proof and do not represent current failures.

The initial author snapshot captured the Lean version and commit prefix, but not the full compiler hash. A later timestamped snapshot records the full hash; none was backdated. The coordinator's fresh verification records the full compiler hash both before and after its own run. The final `largestPrimeFactor` is noncomputable to avoid unnecessary runtime compiler artifacts; its logical definition and greatest-prime-divisor specification are fully checked.

## Report and eligibility

The native editor successfully compiled the final TeX. Tectonic exported it without warnings or box diagnostics; every one of the three rendered pages and the complete extracted text was checked. `verification/export-pdf.py` can reproduce export and rendering with explicit `--report`, `--evidence`, `--tectonic` and `--poppler-dir` paths. Use a separate directory containing a copy of `main.tex` to preserve the submitted PDF bytes. Omit `--native-confirmation` in an independent export: the script cannot invoke the native editor or perform visual inspection and correctly leaves newly exported output awaiting review.

The initial candidate-specific public-history audit found no prior same-problem submission or invalid attempt requiring an error account. Live delta checks compare the main commit, complete PR/issue catalogs, public refs, discussions, prior lead feedback and pending personal PR feedback against that audit. An unchanged commit/ref pins the exact previously checked contents and history. Identifier searches are repeated. Both complete dated contribution guides and the exact bilingual source are included. A fresh final delta check is required immediately before publication; unexpected changes require renewed inspection. Timestamped public observations cannot certify deleted, private or inaccessible material.

`verification/SHA256SUMS.json` binds every other submitted file. The independent review binds the frozen input manifest. All mathematical work is in Lean: no numerical search or external computation supplies a hypothesis or conclusion. The auxiliary code performs inspection, reproducibility checks and report export. These records establish local validation, not maintainer acceptance.
