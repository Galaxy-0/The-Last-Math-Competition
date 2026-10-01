This is the round-wide QA record for both papers. This package contains its own paper and compiler log; the aggregate QA JSON records both checked hashes.

# PDF quality assurance - TLMC round 20260921

Checked at 2026-09-20T17:25:29.550921+00:00.

Both final paper drafts were genuinely compiled from their adjacent LaTeX sources by pinned Tectonic 0.17.0. The PDF skill marker ran successfully once for this batch of 2 PDFs before authoring. Final builds used only cached dependencies and exited with code 0.

| Document | Pages | Bytes | Offline compile | Layout |
|---|---:|---:|---:|---|
| problem2320.pdf | 2 | 48531 | 0.91 s | Pass |
| problem7681.pdf | 2 | 49990 | 0.98 s | Pass |

## Verification

- Every page of each final PDF was rendered with the bundled Poppler and actually inspected.
- Titles, formulas, theorem statements, proofs, references, links, and page numbers are legible; no clipped or overlapping content or missing glyphs.
- Final TeX logs have zero overfull and zero underfull boxes. The pre-existing Fontconfig configuration warning remains; the bundled fonts rendered correctly.
- PDF text extraction confirms both problem identifiers and the named terminal declarations. This checks document consistency, not Lean correctness.
- Changes to the supplied LaTeX were strictly typographic: emergency line flexibility, a line break before the long revision hash in problem 7681, and left alignment for code-heavy paragraphs and references. Mathematical content and theorem names were not changed.
- Full PDF/source hashes and structured evidence are in `final_paper_qa.json`. Compiler output is in `pdf-compile.json` and `proof.log` for this package.
- Any subsequent textual or theorem-name edit requires recompilation and renewed visual QA; these hashes identify the checked versions.

## Hashes

### problem2320
- PDF SHA256: `5b91210bff42a3c9e934444547442b17edfef7ef5e7794401552343af8998d19`
- LaTeX SHA256: `a1036dcc90686d29f92e1875a4d4082d0d898993989a303cbd6c08ef6f0bf1cc`

### problem7681
- PDF SHA256: `f32752e542f2f779d75cd2f215790efc31ae3e2f0edba20886fbd8b9ae71338a`
- LaTeX SHA256: `844d1742c39af3a2400204dc91e31c71d515d8c1a0d48e17e04ad68254e9e77e`
