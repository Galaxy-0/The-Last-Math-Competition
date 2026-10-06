# Verification record

## Mathematical and source scope

The source is conjecture `00000001451` at upstream commit `ba46ce0997cbf232fe95e5dced37ff4d32e1eb94`. `ORIGINAL.md` is byte-identical to that bilingual file (SHA-256 `2b3e65bb53fce2e2c451cf6bd40a1caf7e7b1b3dcb45c0bf5f0672c6bcd590d6`). The exact seven Lean source/configuration identities appear in `verification/source-manifest.json`.

The independent author received only the original statement, current bilingual contribution rules, and pinned runtime/dependency configuration. Prior solutions and selector rationale were excluded. `verification/author-evidence.json` records provenance and transient development failures; the frozen final inputs were independently rehashed.

The theorem preserves the positive exponent, actual symmetric-difference volume condition, genuine geometric facets and attained minimum. It refutes three natural positive-constant readings in dimension two. It does not purport to resolve a corrected negative exponent. No auxiliary numerical computation is used or needed.

## Executed validation

1. The author completed the full mathematical project build, strict source replay, dependency integrity checks, and compiled axiom audit.
2. The coordinator copied only the seven frozen source/configuration files into a new project with no authored build products. A fresh full build, warnings-as-errors replay of `Geometry`, `Vanishing`, `Solution`, and `Audit`, and all nine dependency revision/tracked-clean checks before and after succeeded. Full command outputs are in `verification/root-rebuild.json`.
3. The published `verify.py` was itself executed against the assembled package. All 42 recorded commands passed: toolchain identification, 18 initial dependency checks, fresh build, four strict replays, and 18 final dependency checks. Its inventory agrees exactly with the independent build, including declaration types and complete axiom sets. See `verification/portable-rebuild.json`.
4. Eight validator tests passed: seven mutations are rejected (forbidden axiom, authored axiom, missing declaration, duplicate declaration, unexpected module, changed type, missing module), and the positive test accepts only an unchanged inventory with reordered records/axiom lists. See `verification/validator-negative-controls.json`.

The compiled inventory has **39 mathematical declarations**: 17 from `Geometry`, 10 from `Vanishing`, and 12 from `Solution`. It is derived from compiled module ownership, including generated/private names, rather than a list of theorem names copied from the source. Every transitive axiom set is a subset of `propext`, `Classical.choice`, and `Quot.sound`. No authored axiom, admitted proof, `native_decide`, or unsafe mathematical declaration is used. `Audit.lean` is operational inspection code and is replayed separately; it is not an imported mathematical module.

Lean 4.19.0 and Mathlib v4.19.0 are pinned. Mathlib's exact revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all nine exact revisions appear in `verification/pinned-dependencies.json`. Standard dependencies use their pinned compiled cache, while all authored mathematical modules were freshly rebuilt. The recorded local paths identify where checks ran; the reproduction script uses paths relative to this submission.

## Report and independent review

The standalone LaTeX source compiled successfully in the native editor and exported through Tectonic without warnings. The final PDF has three pages. Every page was visually inspected, and a separate reviewer checked the full source/report/PDF for mathematical correspondence and layout. Exact hashes, native compiler result, export command/output, and export log are in `verification/document-build.json`; independent assessments are in the review records.

## Contribution boundaries

The pull request adds only this personal submission folder. Final external eligibility is recorded separately in `verification/eligibility.json`, with its observation time and public-scope limitations. Public history and status checks establish eligibility within their recorded scope; they do not establish mathematical novelty beyond the repository or maintainer acceptance. The complete raw remote captures are retained locally; their immutable manifest identities are bound in the compact eligibility result. The source, proof, report, mathematical audit, and reproduction tools needed to verify this solution are included here.

`SHA256SUMS.json` binds every submitted file except itself. Review and verification records are local pre-submission evidence, not an official repository reviewer decision.
