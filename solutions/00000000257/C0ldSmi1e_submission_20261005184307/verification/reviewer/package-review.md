# Independent assembled-package review: candidate 00000000257

## Decision

The assembled submission passes the independent completeness, correspondence, and reproducibility review described below. The mathematical disproof, complete Lean project, and matching LaTeX/PDF are approved by this contributor-side independent reviewer. This is a local review decision, not maintainer approval, a merge decision, or a claim of prior acceptance.

The only remaining mechanical step at the time of writing is to generate SHA256SUMS.json after these review documents are copied into the submission, then validate that it covers every supplied file except itself and that all hashes match. The root will supply that final manifest for a read-only validation; the receipt will be kept outside the package to avoid circular changes to its hashes. No mathematical or source revision is requested.

This addendum supersedes the earlier “pending report/PDF/package” status in preliminary-criteria.md, source-review.md, and report-review.md to the extent recorded here. Those documents are preserved as the review history and supply the detailed evidence.

## Material reviewed and exact identities

The entire README.md was read. The reviewer enumerated the assembled submission, including files normally ignored by repository search, and checked 143 files before the final report/package review documents and checksum manifest were added. The reviewed path is:

```text
/Users/daniel/.codex/worktrees/competition-independent/The-Last-Math-Competition/solutions/00000000257/C0ldSmi1e_submission_20261005184307/
```

The README hash at this check was e19bbf187b2f4085a8d2e8379bebfc2b047ba9832fe4bcc0d87df127f65162c7. The final receipt will identify any later nonmathematical assembly additions and verify their final hashes.

The six packaged Lean/configuration files exactly equal the previously frozen source identity record. The main source remains da16f414381ea776c791443eddb3d5ece240af5e6a813bde3ad81c8fdf99ae1f. The packaged conjecture.md is byte-for-byte equal to the initial bilingual input, hash bd613a31cf77b10dba59141cb157ee8aeac43f2703364c63c22a639fb94bf47d. The final report identities remain:

```text
5fcdd6458efc64ad519871f370e245b24b7a9886c0de0029815553bfd76f6167  report.tex
8c23a583e35fa9fd5ce2746b9a676c4d6ec486fdf335371bcc0fe964f8939422  report.pdf
```

The mathematical proof is wholly contained in lean/Conjecture257.lean. lean/Audit257.lean and lean/Check.lean are inspection-only source modules, with complete replay coverage. The pinned toolchain, project targets, and dependency manifest are included. No required mathematical source or configuration file is missing.

## Packaged evidence validation

The reviewer independently performed these checks on the assembled copies, not just their originals:

- verification/frozen-sources.json and verification/audit-names.json exactly equal the frozen records used in the reviewer's clean run.
- verification/independent-verify.py exactly equals the program fully read and independently executed earlier, hash 700055051b4adb8bc2bc36e3a8d394a819ab2bc273ba00a3ceabb3779ee9a144. There is no post-run change to the inspector.
- Both verification/root/ and verification/reviewer/execution/ record PASS and the exact frozen source identities. In each run all 45 command records have zero exit codes and their supplied output logs match every recorded SHA-256 hash. The execution-record files themselves match their recorded hashes.
- Both environment inventories have exactly 22 declarations, including all 17 handwritten declarations and 5 generated logical declarations. All are safe, all axiom sets are subsets of the three standard logical axioms, all transitive issue lists are empty, and the runtime-artifact and unsafe-axiom exemption lists are empty.
- The generated inspection harness matches its recorded hash. It is separate from the mathematical project's imports and supplies no proof assumption.
- All 52 copied reviewer execution-evidence files are byte-for-byte equal to the reviewer's independently produced originals.
- Every copied author provenance/log file is byte-for-byte equal to its original. Earlier failed attempts remain visibly distinct from final success. References to temporary failed source snapshots are historical paths, not missing proof dependencies.
- The packaged PDF build log exactly matches the final log independently inspected, and the PDF validation record identifies the exact reviewed source/PDF and three pages.

The package-check.json retained in the reviewer's private directory records these identity checks. The detailed semantic and trust audit is in source-review.md; the full textual and visual report assessment is in report-review.md.

## README and reproduction commands

The README accurately explains the disproof, full-ring class-number semantics, and final closed theorem. Its declaration counts, allowed-axiom wording, no-exemption claim, and distinction between contributor-side checks and maintainer approval agree with the independently observed evidence.

The documented Lean commands correctly obtain the standard cache, build the two declared default targets, and strictly replay each of the three source modules. The fallback interpreted cache command is the ordinary Mathlib cache invocation. The exact supplied manifest must be retained, as documented.

The optional inspector command supplies every environment-specific argument explicitly: source, fresh build directory, evidence directory, Lean toolchain bin directory, packages, audit inventory, and frozen source manifest. Consequently the retained original-run defaults do not prevent reproduction in a new checkout. Its Python 3.11+ and Git requirements, absent build-directory precondition, and evidence-parent-directory precondition agree with the inspected implementation. As with any command creating an immediate directory, users should choose paths with existing parents.

The documented PDF command is a standard standalone Tectonic compilation. The README correctly notes that timestamps may change the rebuilt PDF's binary hash, and does not misrepresent such a change as a mathematical failure.

No further mathematical computation or auxiliary numerical script needs to run. All mathematical claims are proved in Lean. The sole Python program and generated Lean metaprogram in the package are execution/inspection tools; they were inspected and successfully executed in both recorded clean runs. The existing fresh builds used exactly the packaged source/configuration and byte-identical inspector, so copying those files does not require a redundant third proof build.

## Trust boundary and approval scope

The reviewer confirms the package's explicit limitation: these are clean builds of the submitted project using pinned standard compiler/library artifacts and reused dependency caches; neither independent run rebuilds all of Lean or Mathlib from source. The kernel, exact compiler version, and pinned library artifacts are the ordinary formal-toolchain trust boundary. No proof-specific trust extension, unverified native computation, or class-number oracle is introduced.

The final mathematical statement is a disproof of existence of any positive uniform logarithmic lower-bound constant for the exact field class number in the supplied conjecture. All requirements identified during preliminary scrutiny are satisfied. The source has a genuine quadratic-field model, standard finite ideal class number, proved square-scaling identity, unbounded admissible Pell witnesses, and a strict counterexample for every positive real constant. The complete report/PDF explains the same argument and was independently compiled and visually reviewed on every page.

Subject only to the final mechanical checksum receipt described above, the package is complete and valid for local submission. Publication, prior-solution eligibility, PR state, merge authority, leaderboard edits, and maintainer decisions are outside this reviewer task. The reviewer made no repository or Git mutations and no external posts.
