# Verification record

Prepared and verified on 2026-10-04 UTC with official Lean v4.31.0,
Linux x86_64, commit `68218e876d2a38b1985b8590fff244a83c321783`.

## Lean source and checks

`Ulam205Core.lean` SHA-256:
`af01fea811078f152350626d21498d72935961a7de011874a88e2aecd154382d`

The review revision adds `InSequence`, `range_below_is_earlier`, and
`sequence_global_uniqueSum`. The original construction and main theorem are
unchanged. The added theorem proves full-range distinct-pair uniqueness for
non-seed terms, without extra hypotheses.

On 2026-10-04 the revised source passed both `lean Ulam205Core.lean` and
`lake build` with exit code 0 using a freshly downloaded official Lean 4.31.0
Linux release. Retained logs are `core-build.log`, `lake-build.log`, and
`toolchain.txt`. A separate reviewer independently recompiled the same source
hash and audited the new transfer argument successfully.

The audit confirms all-pairs uniqueness, next-term existence, well-ordering,
exact prefix membership, least choice, infinitude, counting, and uniqueness.
For the selected term, positivity and strict increase force every possible
full-range summand to lie in the earlier prefix. No assertion is made that an
unused top-two witness must remain unique after the prefix grows.

All audited full-proof theorems use only Lean's standard foundational axioms
`propext`, `Classical.choice`, and `Quot.sound`. The uniqueness theorem uses
`propext` and `Quot.sound`. The source has no proof holes, extra axioms, or
`native_decide` uses.

## Report checks

The LaTeX report proves the same least-choice rule, existence, uniqueness,
strict increase, infinitude, exponential upper bound, and logarithmic counting
lower bound. It explicitly distinguishes the integer-scale statement formalized
in Lean from the ordinary real-logarithm corollary written for interpretation.
It states that positive density and existence of a density limit are not proved.
It cites Clément–Steinerberger (2025), §1.2 p. 942, for known classical
infinitude and the same top-two argument; Ross (2016) is retained as background.
It does not claim mathematical novelty.

`report.pdf` was compiled directly from `report.tex` with pdfTeX
1.40.26 (TeX Live 2025/dev/Debian), using two passes. Every rendered page was
visually inspected. The final compiler log has no LaTeX warnings or overfull/
underfull boxes. The cloud image had TeX binaries and packages but lacked its
prebuilt format and generated font maps; these were generated in a temporary
workspace from already installed files. No software download or installation
was needed. A normally configured LaTeX installation uses the ordinary build
command in the README and report.

## Repository status snapshot

Live read-only GitHub API and pinned raw-file check at approximately
2026-10-04 02:45-02:48 UTC:

- Repository HEAD:
  `6ad05f1490626b518d19ad5c5603419f7a021d30`.
- At that pinned commit, `metadata.csv` row `00000000205` reports
  `proven=false`, `disproven=false`, `completed_by_ai=false`.
- The row is retained in `metadata205.csv`.
- `solutions/00000000205` returned HTTP 404 at the same commit.
- The open-PR listing returned PRs 372, 373, and 374, all about other problem IDs.

These observations are a snapshot, not a guarantee against a later or
unindexed competing submission. Recheck before opening the public PR.
Preparation of these files does not itself establish publication or acceptance.

## Final independent report review

An independent reviewer checked the revised LaTeX report, README and bilingual
proof against the revised Lean source and recompiled that source successfully. No mathematical or semantic blocker was
found. The report and source agree on indices, least-choice semantics,
infinitude, uniqueness, and the exact finite counting conclusion. The reviewer
confirmed the disclosed limitations concerning density and novelty.

## Review revision context

Prepared against PR #379 at head
`0dc3e36e5ca4e3f7ec12aff7e9efce805b735440` and review comment
https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/379#issuecomment-5976893523

This revision clarifies the exact semantics rather than changing the sequence
or repairing a mathematical counterexample. The original density wording is
ambiguous; the package continues to claim only its exact logarithmic count.
The earlier repository-status section above is historical and is not the
current PR status. Publication is handled separately after final audit.
