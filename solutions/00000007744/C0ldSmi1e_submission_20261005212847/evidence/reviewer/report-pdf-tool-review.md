# Independent report, PDF, and delivered-tool review

Date: 2026-10-05. This continues `proof-source-review.md`. Verdict for the full mathematical report, all four PDF pages, and the delivered verification tool: **PASS**, with no mathematical or presentation repair requested. Final package-manifest integrity remains a separate coordinator gate.

## Exact report identities

- `report.tex`: SHA256 `9a2774d58ab9454cd57be2e643cdb3ebbf5d764a18f55a2aa77ab8096ac2a67c`.
- Delivered `report.pdf`: SHA256 `01f1a088fc23219d92448b6657fe290d0d6b7be2a07506c6a5190ab37db958d3`.
- The delivered PDF has four A4 pages, no encryption, no forms, and no JavaScript.

The entire LaTeX source, including both quoted source-language statements, all formulas, proof, formalization explanation, verification claims, and references was read. All content agrees with the previously reviewed frozen Lean source. In particular, the report correctly states the conventional simple labelled uniform model, the whole graph sample space, the graphwise identity, actual expectation and law, nonempty unbounded admissible sizes, weak-limit uniqueness, joint-to-marginal implication, necessary-clause interpretation, and the contradiction 0 versus 8/9. It does not claim to refute the first-order Kesten–McKay statement, the existence of every degenerate Gaussian coordinate, or a multigraph model.

## Independent compilation and page review

The source was copied to the independent review directory and compiled using the existing Tectonic binary with `--only-cached --untrusted --keep-logs` and a separate output directory. The actual exit code was **0**. The full stdout/stderr, native TeX log, command and hash receipt are retained under `pdf-review/independent-compile/`.

There is one underfull paragraph (badness 1189, source lines 212–222), reported on the two TeX passes. It creates no overlap, clipping, or missing text. There are no overfull boxes, unresolved-reference warnings, missing-font/glyph warnings in the compilation, or TeX errors.

The independently compiled PDF SHA256 is `586efa7b8192a3567fa105f6434aab119d01aa52644a7bdcf5b22c9180b8d444`. Its file bytes need not match because PDF metadata can vary. More strongly, **all four rendered page PNG hashes match the delivered PDF exactly**, using the same PDFium rendering scale 1.5:

| Page | Matching rendered SHA256 | Visual/content review |
|---|---|---|
| 1 | `6956a0ed4bf1cb8867c3e3388ff85e25fad285e157a97c39673502a564deb862` | Title, abstract, full English and Chinese statements, explicit scope, model definition readable and complete. Chinese glyphs verified. |
| 2 | `8f76bc1b00d51a68296e451f6f8cbb9edabf41dc2c929cd6f925ba98eaeccfb8` | Uniform-model continuation, full deterministic-trace proposition/proof, nonemptiness and weak-limit argument, polynomial definition correct and unclipped. |
| 3 | `acea266cb3dc474e813c218a52760ae113ef4b5e0cd363fb0e0248aadc6dadd7` | Full marginal implication, explicit variance contradiction, general/final theorem statements, trust summary and finite-support table complete and legible. |
| 4 | `fcdd723f329d7205198a13c3dd20c310663a6e243c7e7007bb04b939e16e395f` | Evidence/provenance limitations and both references complete; the mildly stretched paragraph is readable and within margins. |

Every delivered page was independently viewed after rendering. Page numbers and continuation flow are consistent; no black boxes, clipped formulas, overprinted lines, or broken table appear. `pdfium-render-execution.json` binds both PDF hashes to the page-render hashes. Text extracts are retained as a secondary content check, not as a replacement for visual inspection.

### Renderer limitation accurately retained

The initial bundled Poppler render returned exit 0 but warned that its Adobe-GB1 language map was unavailable and omitted Chinese text. Its complete warnings remain in `pdf-review/2.stderr.txt`; this initial render was not accepted. An attempted PyMuPDF fallback returned exit 1 because `fitz` is not installed. The already bundled `pypdfium2` renderer then rendered all text correctly without installation. Thus the first image's missing Chinese was a local renderer configuration limitation, not a defect in the delivered PDF. The coordinator independently used PDF.js with bundled CMaps; this reviewer used PDFium.

## Delivered verification tool inspection and replay

`verification/independent_verify.py` was read completely. Its SHA256 is `8bd7b89e2ac684a15d756bb6bbf14a4738ccca833912d3fd03c0ef42093e8cb4`. The script performs provenance/execution inspection and supplies no mathematical premise. Its generated Lean metaprogram enumerates declarations by actual owning module and records axiom and dependency closures; it is separate from the submitted proof.

The delivered script was run unchanged with explicit CLI arguments for the packaged six-file source project, a new review build directory, a new evidence directory, the authorized Lean runtime and pinned packages, and the delivered audit-name and freeze records. The outer process exited **0** with empty stderr. All 45 recorded internal commands exited 0. The replay confirms:

- All six source/config identities, the exact compiler commit, and all nine dependency revisions match; dependency tracked trees remain clean.
- Fresh full build, strict replay of all three modules, actual printed types/axioms, 19 definitions, 26 theorems and four named instances pass.
- Complete inventory again contains 83 entries, with 75 logical declarations and eight runtime compiler entries. Every logical axiom/safety closure is clean.
- Source, copied files, freeze record, audit inventory, verifier source, runtime identity and dependencies remain unchanged after all checks.

This output agrees with the reviewer's separately authored compiled-body/closure inspector. In particular, the verifier's runtime classification is not the sole evidence: this reviewer previously inspected each of the eight runtime bodies and all generated logical bodies and confirmed no runtime artifact participates in a logical dependency closure.

The outer receipt is `packaged-verifier-execution.json`; detailed receipts and outputs are in `packaged-verifier-evidence/`. The packaged README was also read. Its reproduction commands and mathematical/evidence scope are correct. One optional wording precision was communicated to the coordinator: distinguish the coordinator's PDF.js renderer from this reviewer's PDFium renderer. Reviewer-script/evidence destinations mentioned by the README were still being finalized when it was read and remain part of the final inventory gate.

## Overall mathematical/artifact judgment

The source, compiled Lean proof, complete report, supplied PDF, finite computations, reviewer diagnostics, and delivered verification tool are mutually consistent and provide a complete disproof of the source's necessary quadratic-variance clause in the conventional uniform simple-regular-graph model. No unresolved mathematical, semantic, logical-trust, execution, or visual-layout defect remains from this review. This is an independent local review result, not a claim of maintainer acceptance or authorization to publish.
