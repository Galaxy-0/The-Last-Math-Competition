# Verification

The final coordinator execution rebuilt the project in a fresh directory and replayed all six submitted Lean source files with warnings treated as errors. The explicit source inventory covers 62 authored declarations: 15 definitions/abbreviations and 47 theorems, with no custom instances. `Check.lean` prints the definition bodies, all theorem types and their axiom dependencies; `Audit240.lean` prints axioms for all 62 authored declarations.

The complete compiled-module inventory covers 103 declarations, including 41 generated declarations. It uses actual module-of-origin information, not a namespace-prefix filter. Every compiled declaration's full type, safety flags and axiom set is preserved. Every logical type/body dependency is traversed, including inductive declarations and recursor rules. Only `propext`, `Classical.choice` and `Quot.sound` occur. There are no admitted proofs, custom axioms, `native_decide`, or unsafe/partial logical dependencies. 15 compiler-generated runtime stages remain explicitly inventoried and are separately identified; none supplies a mathematical premise or theorem, and their axiom sets are checked too.

Lean is 4.19.0, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`. The actual compiler binary SHA-256 was `5c1fe58db7d10b1cd0ddff1a1cbc49db2396fff9c6c983cc3b49f1c5c1ae241b` on arm64 macOS. Mathlib is v4.19.0, revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine actual dependency revisions and tracked-source cleanliness were checked before and after verification. Cached dependency artifacts were reused; this is not a rebuild of Lean or all Mathlib from source.

## Reproduce the proof

With the pinned Lean toolchain installed, run from `lean/`:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Geometry240.lean
lake env lean -DwarningAsError=true Objects240.lean
lake env lean -DwarningAsError=true Volume240.lean
lake env lean -DwarningAsError=true Conjecture240.lean
lake env lean -DwarningAsError=true Audit240.lean
lake env lean -DwarningAsError=true Check.lean
```

Keep all manifest revisions fixed. Both inspection modules only print existing definitions, types or axiom information; they prove no mathematical result.

## Reproduce the full trust audit

From the submission directory, with Python 3.11 or later and Git available, replace the tool path below with the pinned Lean toolchain directory. The build directory must not already exist.

```sh
python3 verification/independent-verify.py --ready \
  --source "$PWD/lean" \
  --build-dir /tmp/tlmc240-fresh-build \
  --evidence-dir /tmp/tlmc240-fresh-evidence \
  --lean-bin '<directory containing pinned lean and lake>' \
  --packages "$PWD/lean/.lake/packages" \
  --audit-names "$PWD/verification/audit-names.json" \
  --frozen-sources "$PWD/verification/frozen-sources.json"
```

This checks all source/configuration identities and actual dependency revisions, then builds and strictly replays every module. The generated `IndependentEnvironmentInventory.lean` is inspection metaprogramming outside the proof's imports. It enumerates all constants originating in the submitted modules and traverses their logical dependencies. Its own runtime inspection implementation is not a proof axiom. Exact command transcripts, timestamps and statuses are preserved in `verification/execution-transcripts.json`; paths inside historical records identify the original execution environment. Those transcripts preserve the exact raw text and hashes for each referenced log.

## Reproduce independent numerical corroboration

```sh
python3 reproduce.py
```

Only Python's standard library is required. Every decision uses exact fractions. The script enumerates all supporting facets, verifies that each vertex is extreme, checks primal/polar vertex-facet duality in both directions, constructs complete face lattices and sums barycentric-simplex determinant volumes. Independent section formulas agree. Reference cube/cross-polytope volumes and a nonsingular rational shear check normalization. Expected body/polar volumes are `8/3` and `4`, with Mahler product `32/3`; the script must return `"result": "PASS"` and exit 0. The Lean theorem does not assume these computed values: it proves ordinary Lebesgue volume identities.

## Development history and correction

The author's frozen original project passed its complete build, strict source replays and all 62 authored axiom checks. The coordinator's stronger first environment audit additionally found four unsafe compiler-generated specialization axioms for `axis` and `dot`. They were absent from the authored mathematical statements and logical proof dependencies, but failed the conservative complete-environment check. The coordinator added only explicit `noncomputable` modifiers to those two definitions, suppressing unnecessary executable specializations. Definition bodies, theorem statements and proof bodies remain byte-for-byte unchanged after removing those two modifiers. The unchanged verifier then checked the final source afresh. Exact original/final hashes, differences and the failed gate are preserved in `coordinator-amendment.json` and `coordinator-attempts.json`.

`author-history.json` preserves all author's historical text files, source snippets, captured stdout/stderr, logger source and 108 command records, including failed development attempts. It is historical evidence, not a set of final reproduction commands. The initial directory listing/logger bootstrap and one shell parse failure preceded the wrapper logger. Their surviving tool outputs and exit statuses are reconstructed separately with unknown wall-clock timestamps explicitly marked; no timestamps were fabricated. This does not affect the fully recorded final mathematical checks.

The report initially had one TeX error (a math macro in text mode), which was corrected. The final source compiled successfully in the native editor and exported without warnings or box diagnostics. All four rendered pages and the complete extracted text were inspected. `verification/export-pdf.py` can reproduce export/rendering with explicit `--report`, `--evidence`, `--tectonic` and `--poppler-dir` arguments. Use a separate directory containing a copy of `main.tex`; omit `--native-confirmation` for your own export. The script cannot invoke the native editor or perform visual inspection, and correctly leaves new output awaiting review. Text extraction used pypdf after the bundled pdftotext executable was found unavailable.

## Source fidelity, eligibility and acceptance

The source uses actual compactness, real convexity, nonempty interior, origin symmetry, the standard dot-product polar and coordinate Lebesgue measure. Explicit lemmas prove the coordinate map, dot product, cube/cross inequalities, ambient dimension and measure preservation. The two actual volumes are proved finite before conversion to real-valued measure. The image obstruction quantifies over every linear endomorphism, including singular maps.

The public-history eligibility audit found no prior same-problem submission or invalid attempt requiring an error account. Final delta checks compare current main, complete PR/issue catalogs, public fork refs, mutable discussion/review inputs and the candidate searches with that audit. Unexpected changes require renewed inspection. Both complete dated contribution guides and the exact source are included. Public observations are timestamped and cannot certify deleted, private or inaccessible material.

The separate nonauthor review records its own execution and semantic findings and binds the final review-input manifest. `verification/SHA256SUMS.json` binds every other submitted file. These are local checks; maintainer acceptance remains a separate decision.
