# Public submission of conjecture 00000000508

Submitted by GitHub user **@lizaixi01** with AI assistance from OpenAI Codex.
Mathematical reasoning, Lean code, reports, semantic review and packaging are AI-assisted.
The independent semantic review is by a separate AI agent, not a human mathematician.
Status before organizer review: **locally_verified**. Upstream acceptance is not claimed.

## Result and exact scope

The exact Bayer-Charalambous-Popescu extremality definition is proved equivalent to maximal shifted support, then gives an antichain for every numerical Betti table. This specializes to every monomial ideal without an extra support premise. Positions are the standard (k,d) coordinates for beta_(k,k+d), with product order, corroborated by BCP99 pp.1-2. Raw (k,j) coordinates have a different order and are not claimed. The result is a known structural fact; no new-mathematics claim is made.

Final target: `TLMC508.exact_raw_definition_antichain`.

## Reproduction

Install the toolchain named in `lean/lean-toolchain` (Lean 4.33.0). From the
`lean/` subdirectory run `lake build +Main`. Lake downloads the exact Git
dependency revisions in `lake-manifest.json`; do not update those pins.
The project includes all local imported Lean modules and excludes every `.lake`
cache and author-produced `.olean`. The original clean build, exact target-type
contracts, transitive axiom audit and official fresh kernel replay passed for
the frozen source bytes. Only the standard axioms propext, Classical.choice
and Quot.sound occur (a subset suffices for some targets).

For a further official kernel replay use `lake env leanchecker --fresh Main`
with the pinned toolchain after building. Compile `proof.tex` with Tectonic 0.17
or a compatible LaTeX installation. The supplied two-page PDF is the unchanged,
compiled and visually verified original. Historical clean-network reproduction
on a separate machine was not tested; Git-based dependency locks are portable.

## Frozen materials and provenance

Every original package file included here, including `README.md`, Lean sources,
dependency locks, LaTeX, PDF, original problem and source correspondence, is
byte-identical to the locally validated frozen version. The local log files
`proof.log` and `proof.compile.json`, when present, are omitted from publication;
the actual build and replay outcomes remain in the copied evidence receipt.
Added files are this publication note, LICENSE, copied evidence and SHA256.json.
Evidence copies replace machine-specific paths with placeholders; the local
raw receipts remain sealed and their SHA256 values are recorded below.

The frozen README/report contain historical local-draft wording and sometimes
refer to worker files outside the sealed package. These statements describe the
pre-publication audit, not a missing mathematical assumption. This note supplies
the current public reproduction instructions. No theorem, proof or PDF was
rewritten for publication. Documented same-project prior work is credited in
the report and correspondence; no new mathematical discovery is asserted.

Raw local receipt SHA256: `43ce1cecd544c7bb8c6b2ddd78cb88386f68a3836662095b6e1b8b1931b2cceb`.
Raw local semantic-review SHA256: `8e9c110ed2f916c6d01b39142798addd9d64731815ddc8c492f075146bd38e1e`.

## Submission eligibility snapshot

Official upstream commit: `45a97edf95fb8adc2a2a02412753b109f728d662`.
Both metadata solved flags are false; the complete current Git tree has no
solution folder for this ID; all 841 historical PRs, including
closed/merged PRs and previous filenames, were checked for this solution path.
The 11,411-file PR #267 was checked by complete merge-base/head tree comparison
because the PR files API is capped at 3,000. No previous submission for this ID
or corresponding solution-folder history was found. This is a repository-level
eligibility check, not a worldwide mathematical-priority claim.
