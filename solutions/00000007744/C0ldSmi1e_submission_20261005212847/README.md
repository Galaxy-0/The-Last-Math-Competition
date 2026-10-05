# Disproof of conjecture 00000007744

For every simple d-regular graph on n vertices, the actual adjacency matrix satisfies `trace(A²) = nd`. Its centered quadratic trace is identically zero under the whole uniform graph model, for any deterministic adjacency/trace normalization. The actual laws are Dirac at zero at every size, and uniqueness of weak limits forces limiting variance zero. At d = 3 the conjecture prescribes 8/9.

The formalization includes arbitrary polynomial traces, actual uniform expectations and pushforward laws, finite-dimensional joint laws and continuous marginal projection, and nonempty uniform ensembles on an unbounded family of vertex sets. The block graph is only a nonemptiness witness: sampling is over **all** regular graphs. `RequiredSecondOrderLimit` is explicitly a necessary part of the original conjunction, not a replacement definition of its other covariance/Gaussian requirements. Its negation refutes that conjunction.

The model is the conventional labelled simple, undirected regular-graph model. No theorem about an unconditioned multigraph configuration model is asserted. The first-order Kesten–McKay statement is not claimed false. Read both language versions in `original_conjecture.md` and the complete four-page `report.pdf` (`report.tex` is the matching source).

## Reproduce the Lean proof

The project pins Lean **4.19.0**, compiler commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, and Mathlib **v4.19.0**, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All nine dependency revisions are locked in `lean/lake-manifest.json`. With Elan/Lake available, run from this submission folder:

```sh
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true Conjecture7744.lean
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true Check.lean
cd ..
```

`lakefile.toml` also enables warnings as errors. `Conjecture7744.lean` contains the mathematical proof. `Audit.lean` prints axiom dependencies for all 49 authored declarations. The coordinator added inspection-only `Check.lean`, which prints 19 definitions and the types and axioms of 26 theorems and four named instances. It adds no proof facts. The final theorem is `Conjecture7744.conjecture7744_false`; the general result is `Conjecture7744.no_required_second_order_limit`.

For a separate fresh build and complete compiled-declaration audit, run the delivered verifier with explicit paths. Python 3.11 or newer is required. The two output directories below must not have been used for an earlier verification:

```sh
tlmc7744_submission="$PWD"
tlmc7744_runtime="$(cd lean && dirname "$(elan which lean)")"
tlmc7744_audit="$(mktemp -d)"
python3 verification/independent_verify.py --ready \
  --source "$tlmc7744_submission/lean" \
  --build-dir "$tlmc7744_audit/proof" \
  --evidence-dir "$tlmc7744_audit/evidence" \
  --lean-bin "$tlmc7744_runtime" \
  --packages "$tlmc7744_submission/lean/.lake/packages" \
  --audit-names "$tlmc7744_submission/verification/audit-names.json" \
  --frozen-sources "$tlmc7744_submission/verification/frozen-sources.json"
```

This tool verifies exact source/configuration identities, the compiler and all nine dependency revisions, a fresh build, strict replays, declaration coverage, and transitive axiom/safety closures. Its generated Lean inspection commands only inspect existing declarations; they do not prove the submission's theorems.

The full compiled inventory has **83 entries**: 49 authored declarations and 34 generated entries. **75 are logical declarations**, with only `propext`, `Classical.choice`, and `Quot.sound` (or no axioms), no unsafe/partial/missing logical dependencies, and no extra axiom declarations. The remaining eight are ordinary compiler runtime wrappers, individually inspected by the independent reviewer and retained in the inventory. They and their proof-erasure/compiler placeholders do not occur in any logical dependency closure. No author proof uses `sorry`, `admit`, `native_decide`, custom axioms, or an unsafe/trust bypass.

## Supporting computations and reviewer checks

```sh
python3 verification/check_small_ensembles.py
python3 verification/independent_count_check.py
```

The first script exhaustively enumerates all labelled simple cubic graphs on four and six vertices and computes every entry of the squared adjacency matrix, exact expectations, and centered variance using integers and fractions. It finds 1 and 70 graphs, respectively, normalized trace 3, and variance zero. The second, independently written script instead checks all edge masks and additionally verifies that the six-vertex complements consist of 60 six-cycles and 10 pairs of triangles. These are finite supporting calculations, not the asymptotic proof.

The independent reviewer also supplied `verification/reviewer/ReviewerBridge.lean`. After building the project, it can be checked from `lean/` with:

```sh
lake env lean -DwarningAsError=true ../verification/reviewer/ReviewerBridge.lean
```

That diagnostic proves the same cubic-law contradiction for arbitrary sequences of nonempty finite label sets and checks the usual convergence reindexing step. It is review evidence; the submitted proof does not import it.

## Report and evidence

`report.tex` compiles in the Codex built-in LaTeX editor. The matching supplied PDF was exported with the existing Tectonic compiler. The coordinator rendered it with PDF.js and bundled Chinese CMaps; the independent reviewer used pypdfium2. Both visually inspected all four pages. The reviewer also independently recompiled the report and verified that all four rendered page hashes match the supplied PDF. To produce another PDF with Tectonic, use `tectonic report.tex` in a separate copy/output directory. A harmless underfull-paragraph warning was visually checked; no text is clipped or overlapping.

- `evidence/input/`: exact contribution guides, pinned dependency template and clean source-only input identity records.
- `evidence/author/`: original author commands, actual exit codes, diagnostics, final-stage snapshots, semantic explanation and inventory. Its original inventory covers five project files before the coordinator added `Check.lean`.
- `evidence/coordinator/`: independent fresh build, every strict replay, named audits, complete compiled environment/closure inventory and exact standard-library definition extracts.
- `evidence/finite/`: the supporting exhaustive calculation and its execution metadata.
- `evidence/reviewer/`: independent source-first criteria, mathematical review, fresh execution, all compiled bodies/closures, alternate enumeration, reviewer bridges, and auxiliary-tool replay records.
- `evidence/pdf/`: successful native compiler and export records, matching report/PDF identities, rendering and full-page inspection records.
- `verification/`: distributable audit and auxiliary source code, with source inventory and the six-file freeze record.
- `SHA256SUMS.json`: SHA-256 identities for every final package file except the manifest itself.

The author's historical `run.py` and `verify.py` in `evidence/author/` retain their original local paths and are evidence scripts, not the recommended portable entry points. The reviewer replayed the five-file validator in an isolated copy using exactly two documented path substitutions and preserved its original result. Earlier failed author commands and diagnostics survive, but their overwritten draft source versions were not retained; contemporaneous snapshots begin at final verification. Neither those failures nor reconstructed inputs are presented as successful original tests. Final-source verification is independently reproducible through the commands above.

Before publication, current source/rules/metadata and prior-submission eligibility are checked again against the exact committed package. All repository changes are confined to this personal submission folder. Local validation and independent review here are not claims of maintainer acceptance.
