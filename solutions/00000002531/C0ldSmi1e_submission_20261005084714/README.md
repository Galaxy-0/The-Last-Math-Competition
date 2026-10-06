# Disproof of conjecture 00000002531

With the source's denominator r^k and standard normalized Hausdorff measure, the real line with k = 1 has density 2 everywhere. No null exceptional set makes that density belong to {0,1}. The two-page report and formal proof explicitly disclose the Euclidean, normalization, ball and positive-radius conventions left implicit in the source.

The result refutes a necessary first assertion of the conjunction. It does not separately settle the later exceptional-dimension or sharpness assertions. The source places no finite-total-measure restriction on E; every ball numerator in the counterexample is finite.

## Contents

- `conjecture.md`: complete unchanged English and Chinese statement.
- `main.tex`, `main.pdf`: matching report with the argument, conventions and formal correspondence.
- `lean/`: complete Lean 4.19.0 / Mathlib v4.19.0 project and exact dependency revisions.
- `SEMANTIC_REVIEW.md`: independent internal review, distinct from maintainer acceptance.
- `verification.txt`, `verification/`: full execution, declaration, auxiliary, report and timestamped eligibility records.

The main declarations are `Conjecture2531.counterexample`, `not_borelDensityClause`, and `not_caratheodoryDensityClause`. The Borel and Caratheodory propositions are explicitly necessary specializations to the real line. The generic implication/conjunction theorems formalize the logical disproof step; the connection from the natural-language source to that necessary clause is explained semantically in the report and review.

## Reproduce the proof

With the pinned Lean toolchain installed, run from this submission directory:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture2531.lean
lake env lean -DwarningAsError=true Check.lean
lake env lean -DwarningAsError=true ../verification/author/Inspect.lean
```

The default build covers every mathematical module. `Check.lean` and `Inspect.lean` print genuine definitions, theorem types and axiom dependencies. No numerical experiment or external mathematical certificate is required.

For the independent execution/dependency audit, use Python 3.11 or later, start in the submission directory, and replace the compiler path below. The build output directory must not already exist; choose a fresh directory for each run.

```sh
python3 verification/independent-verify.py --ready \
  --source lean --build-dir /tmp/tlmc2531-rebuild \
  --evidence-dir /tmp/tlmc2531-recheck \
  --lean-bin /absolute/path/to/lean-4.19.0/bin \
  --packages lean/.lake/packages \
  --audit-names verification/audit-names.json \
  --frozen-sources verification/frozen-sources.json
```

The verifier rebuilds this project from fresh outputs, then inventories every compiled declaration originating in its implementation module, including generated constants. It traverses logical type/body dependencies and checks exact source, compiler and dependency identities before and after. It reuses pinned dependency artifacts: it does not rebuild Lean or all of Mathlib. Its Lean metaprogramming only inspects the already checked environment and proves no submitted theorem.

## Reproduce the report

Compile `main.tex` with a standard LaTeX compiler. To repeat the recorded Tectonic export and Poppler rendering, copy `main.tex` to a scratch report directory, then run:

```sh
python3 verification/export-pdf.py \
  --report /absolute/path/to/scratch-report \
  --evidence /absolute/path/to/scratch-pdf-evidence \
  --tectonic /absolute/path/to/tectonic \
  --poppler-dir /absolute/path/to/poppler/bin
```

This helper checks compiler diagnostics and renders every page. It leaves visual review pending until a person or reviewing agent actually inspects the pages. The original native-editor compilation is recorded separately; the helper does not claim to invoke it. PDF metadata can change its hash between exports; source identity, successful compilation, complete text and every rendered page were checked for the submitted PDF.

Recorded absolute scratch paths are historical provenance. The commands above accept replacement paths. The complete source-file checksums appear in `verification/SHA256SUMS.json`. Eligibility is a timestamped observation of accessible public records, not a guarantee about inaccessible or future submissions.
