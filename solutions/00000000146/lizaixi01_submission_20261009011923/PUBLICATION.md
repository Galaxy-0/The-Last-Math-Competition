# Public submission of conjecture 00000000146

Submitted by GitHub user **@lizaixi01** with AI assistance from OpenAI Codex.
Mathematical reasoning, Lean code, reports, semantic review and packaging are AI-assisted.
The independent semantic review is by a separate AI agent, not a human mathematician.
Status before organizer review: **locally_verified**. Upstream acceptance is not claimed.

## Result and exact scope

The literal primes p<=N, denominator N and multiplier N are retained. On the standard KS threshold domain [0,1], the actual measurable statistic escapes uniformly; its genuine pushforward has no real probability weak limit under any, even N-dependent, probability laws of alpha. This also rules out a real-valued Brownian-bridge functional. The omitted threshold convention and normalized bounded-continuous-test formulation are explicitly disclosed.

Final target: `Route2.no_probability_weak_limit`.

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

Raw local receipt SHA256: `3d2b8a373b14bb760a7edbb5609084e414b704b5783f4b663491ca037e8fde25`.
Raw local semantic-review SHA256: `88b8b51537196cb2c4597eb2e23753f177134cac9c34187183dcded9407ec63c`.

## Submission eligibility snapshot

Official upstream commit: `45a97edf95fb8adc2a2a02412753b109f728d662`.
Both metadata solved flags are false; the complete current Git tree has no
solution folder for this ID; all 841 historical PRs, including
closed/merged PRs and previous filenames, were checked for this solution path.
The 11,411-file PR #267 was checked by complete merge-base/head tree comparison
because the PR files API is capped at 3,000. No previous submission for this ID
or corresponding solution-folder history was found. This is a repository-level
eligibility check, not a worldwide mathematical-priority claim.
