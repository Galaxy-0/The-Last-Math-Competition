# Verification record

Prepared and verified on 2026-10-04 UTC with official Lean v4.31.0,
Linux x86_64, commit `68218e876d2a38b1985b8590fff244a83c321783`.

## Lean source and checks

`Ulam205Core.lean` SHA-256:
`ddbc155f051e41efb27b719b3d08df58d1f33836d8e7f13bd551718863f0a887`

The final submission preserves the previously independently checked Lean source
byte for byte. In the final submission directory, both of the following were
run again on 2026-10-04 and exited 0:

- `lean Ulam205Core.lean`
- `lake build`

The logs are `core-build.log` and `lake-build.log`. The minimal Lake project
has no external dependencies. `toolchain.txt` records the compiler version.
The build cache is excluded from the submitted files.

A separate reviewer previously compiled this final Lean hash and checked:

- distinct unordered summand pairs match the standard rule;
- the two-largest-values lemma guarantees a candidate without assuming
  infinitude;
- well-ordering selects the least admissible candidate;
- each recursive state contains exactly the earlier sequence values;
- the combined theorem proves infinitude and the finite counting estimate for
  that same sequence;
- strong-induction uniqueness uses equality of the candidate sets.

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
It cites Daniel Ross's 2016 dissertation for the known infinitude fact and does
not claim mathematical novelty.

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

An additional read-only reviewer checked the completed LaTeX report against the
Lean source, recompiled the unchanged source successfully, and verified the
university dissertation citation. No mathematical or semantic blocker was
found. The report and source agree on indices, least-choice semantics,
infinitude, uniqueness, and the exact finite counting conclusion. The reviewer
confirmed the disclosed limitations concerning density and novelty.
