# Disproof of conjecture 00000009700

An algebraically independent set of transcendental real numbers need not have Hausdorff dimension one. A nonempty singleton of a rational-transcendental real has dimension zero. The report explicitly uses the ordinary real/rational conventions, because the source does not name its ambient space or coefficient field.

The original English and Chinese statements have no infinitude or maximality condition. The formal result refutes their necessary first dimension clause. It also proves the logical obstruction to every further conjunct on the same qualifying sets, without assigning a definition to the unspecified box-dimension spectrum.

## Contents and formal correspondence

- `conjecture.md`: complete unchanged bilingual source.
- `main.tex` and `main.pdf`: matching two-page report.
- `lean/`: complete Lean 4.19.0 / Mathlib v4.19.0 project with pinned dependency revisions.
- `SEMANTIC_REVIEW.md`: separate independent internal review; this is not maintainer acceptance.
- `verification.txt` and `verification/`: exact source identities, complete execution and declaration records, auxiliary checkers, PDF evidence, and timestamped eligibility records.

All new declarations are in namespace `Conjecture9700`. `HausdorffClause` quantifies over actual real sets and retains both algebraic-independence and member-transcendence hypotheses. `exists_nonempty_counterexample` proves a genuine nonempty witness. `hausdorff_clause_false` is the main negation; `universal_conjunction_false` provides the arbitrary-conjunct logical bridge. The dimension function in the pinned library is the root-level `dimH`; see the naming clarification preserved with the original preassessment.

## Build and inspect

With the pinned Lean toolchain installed, run from this submission directory:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture9700.lean
lake env lean -DwarningAsError=true Check.lean
```

`Check.lean` prints the exact definition, theorem types, and axiom dependencies. The default build covers the complete mathematical proof. No numerical computation, generated certificate, or external mathematical calculation is required.

For the additional checker, run from the submission directory, replacing the compiler path:

```sh
python3 verification/author/verify_author.py --project lean --lake /path/to/lean-4.19.0/bin/lake --output /tmp/conjecture9700-author-check
```

For a fresh build plus complete declaration and transitive-dependency audit, choose a build directory that does not yet exist, then run:

```sh
python3 verification/independent-verify.py --ready \
  --source lean --build-dir /tmp/conjecture9700-fresh \
  --evidence-dir /tmp/conjecture9700-audit \
  --lean-bin /path/to/lean-4.19.0/bin \
  --packages lean/.lake/packages \
  --audit-names verification/audit-names.json \
  --frozen-sources verification/frozen-sources.json
```

The script checks all nine dependency revisions and tracked working trees, compiler identity, strict source replays, every compiled declaration, every axiom closure, transitive type/body dependencies including recursor rules, and unchanged source/configuration hashes. Its generated inspection harness is outside the submitted proof project and proves no mathematical theorem. The recorded run uses explicit local runtime paths; the CLI options above make those locations replaceable.

## Report and integrity

`tectonic main.tex` regenerates the PDF. The optional `verification/export-pdf.py` also renders every page; its `--report`, `--evidence`, `--tectonic`, and `--poppler-dir` options select local paths. A normal reproduction records that it did not invoke the Codex native compiler. The supplied native-compilation record separately binds the observed successful editor compilation to the exact TeX hash. PDF creation metadata can vary between runs.

`verification/SHA256SUMS.json` records every other submitted file. The frozen review-input manifest binds the exact files supplied for independent scrutiny. Eligibility is a timestamped observation of accessible public history, with stated coverage limits. Local verification and internal review do not constitute maintainer acceptance.
