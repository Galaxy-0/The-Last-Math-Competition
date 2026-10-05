# Independent final report and PDF review — 00000000525

**Decision: PASS for the complete report, README, and four-page PDF.** The final submission-wide manifest still awaits a separate integrity receipt. No managed-checkout file was modified by this reviewer.

Reviewed personal package:

`/Users/daniel/.codex/worktrees/competition-explore/The-Last-Math-Competition/solutions/00000000525/C0ldSmi1e_submission_20261005203313/`

Exact reviewed report source SHA-256: `bcc49b449d742d1b11371821251c9d321487d1ce781ddd467cb5a81a7e2cbc1a`.

Exact reviewed PDF SHA-256: `2223ffbaace4a8ebc14ca0038fa8dfad26862ad33e28576b5f978a98d6861c61`.

The complete README and report LaTeX source were read. The original bilingual source in the package was compared byte for byte with the original frozen input and matches exactly. The report's typographic mathematical transcription preserves both languages' meaning and quantifiers. The report and README accurately distinguish the full conjecture's negation from its separate limiting assertion and do not claim an exact threshold value.

The actual package PDF was independently rendered into a new reviewer directory, `/private/tmp/tlmc525-review/pdf-review/`, without reusing or overwriting the coordinator's page renders. `pdfinfo` confirms four A4 pages, no encryption, no JavaScript, and no forms. The exact PDF hash was checked before rendering.

The preferred Poppler renderer ran but lacked this runtime's Adobe-GB1 CMap language data, producing recorded errors for Chinese glyphs. This was an environment rendering limitation. The separately executed PDF.js renderer with bundled Adobe CMaps and the bundled canvas library correctly rendered all four pages, including the entire Chinese source. Every one of those four independently rendered images was then opened and visually inspected. Acceptance does not rely on the deficient Poppler output or on text extraction alone.

## Page-by-page review

| Page | Content and checks | Result |
| --- | --- | --- |
| 1 | Title, author, date, abstract, full bilingual conjecture, literal-scope discussion, all-level threshold definition, real normalization, genuine polynomial/ideal interpretation. Chinese glyphs, superscripts, brackets, and the definition display are legible and correct. | PASS |
| 2 | Complete polynomial identity, ideal membership, all-level Frobenius propagation, exponent bound, nonempty/bounded supremum argument, strict 4/5 < 5/6 comparison, and e=0 indexing bridge. All powers and denominators match the Lean argument. No clipped displays or obscured notation. | PASS |
| 3 | Genuine bracket ideal, all-maximal-ideal infimum, explicit F-finite regular scope, cited equivalence boundary, local set conditions, actual origin ideal, and the exact global≤origin comparison. Every claimed formal result matches the reviewed declarations. The wrapped long lemma name remains readable. | PASS |
| 4 | Prime-subtype and limit-filter scope, final theorems for every real L, exact reproduction command and module names, pinned versions, 48+15=63 audit summary, three standard axioms, absence of proof bypasses, inspection-only tooling, and both references. Commands and bibliography are fully legible; the page is complete with no overflow. | PASS |

All pages have consistent readable typography and margins, clear section transitions, correct page numbers, and intact mathematical symbols. There are no overlapping blocks, missing text, clipped commands, unrendered source, placeholder references, or unreadable Chinese characters in the successful independent render.

## Mathematical and reproducibility claims

The report's argument is complete and agrees with the independently reviewed proof: a characteristic-five all-level upper bound refutes the universal residue equality, hence the conjunction. The real supremum set's nonemptiness and boundedness, positive-level equivalence, maximal-ideal infimum's nonemptiness/lower bound, and direction of the origin comparison are explained correctly. The report explicitly states that it formalizes a standard full characterization and cites, rather than formalizes, its equivalence with the test-ideal definition. It neither expands the cited F-finite result to arbitrary fields nor silently asserts equality of local and global thresholds.

The README's reproduction instructions match the project targets, exact dependency pins, and inspection-file names. Its optional dependency-cache command is correctly separated from the kernel-checked mathematics. The full-verifier command supplies all path overrides required for a new machine and warns that its output build directory must be fresh. Historical absolute paths are accurately described as execution evidence rather than portable defaults.

The document export identity record ties this exact LaTeX hash to this exact PDF hash, with native-editor compilation success and a successful final Tectonic exit. I inspected the final export output and log; there are no actual final layout warnings. The earlier missing-font export failure and unsuccessful layout attempt are kept separately. These past failures do not appear as successful final validation.

The package's five frozen author Lean/configuration files still match every original frozen hash. `Check.lean` matches the copy independently replayed by this reviewer. The packaged verifier matches the program already read and reviewed. The 45 coordinator execution records were checked: all contain exit code zero, agreeing with the report. Reviewer execution claims agree with this reviewer's own logs, including the separate documented repair of an output-only pretty-printer option.

The README's reference to a complete reviewer record is fulfilled by inclusion of this report alongside the earlier formal review. Its final `SHA256SUMS.json` claim must be checked when that manifest is supplied; it is intentionally not accepted in advance.

Machine-readable report/PDF identity and per-page render hashes are in `report-pdf-acceptance.json`. This completes the previously outstanding document gate in `formal-review.md`, conditional only on unchanged reviewed bytes and the separate final package integrity check.
