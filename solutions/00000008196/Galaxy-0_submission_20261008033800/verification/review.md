# Verification and independent semantic review

Date: 2026-10-08 Asia/Shanghai (2026-10-07 UTC).

## Result and scope

The literal Staudt-hit predicate is p−1 dividing k. At primes 5 and 17, exact counts in every nonempty sample of the first 8m positive even indices are 4m, m and m. Joint probability is 1/8 rather than product 1/16. The finite counting independence law is false at every positive m, with arbitrarily large counterexamples.

The source leaves its probability model unspecified. The result concerns the explicitly disclosed standard uniform-cutoff/natural-density reading. Real limits, a general probability-space library and Bernoulli-number theory are not formalized; they are not silently claimed as formal coverage. The report explains the elementary natural-density consequence. Degenerate alternative laws are explicitly excluded from the claim.

## Formal semantics

- `IsPrime` uses the ordinary divisor characterization; the exact primes 5 and 17 are kernel-checked.
- `hit_iff_dvd` connects the executable event to the source's divisibility predicate.
- `evenSample_initial_segment` proves exact equality with the list j↦2(j+1) over j=0,…,8m−1. This is a genuine uniform initial-segment sample, not a substituted collection of unrelated cases.
- `exact_counts` is symbolic in unbounded m, rather than a finite regression assertion.
- `nested_obstruction` covers every finite list with positive 17-hit count and non-certain 5-hit count.
- `not_independent` requires m>0; the empty-sample loophole is excluded.
- `arbitrarily_large_counterexamples` proves there is no finite sample-size threshold after which the law holds.

## Actual validation

1. Fresh submission directory with no prior `.lake` build: `lake build` exited 0 under the official Lean 4.31.0 toolchain.
2. `lake env lean -DwarningAsError=true Main.lean` exited 0.
3. A separate mathematical reviewer independently read the full final source and report, then ran the pinned `lean -DwarningAsError=true Main.lean`: exit 0, no warnings.
4. The four printed main/counting theorem axiom lists are exactly `propext`, `Quot.sound`. No extra axiom or admission occurs.
5. Independent Python exact-arithmetic regression checked primality, nesting and counts for N=1,…,1000. Every one of the 125 multiples of eight had discrepancy 1/16.
6. LaTeX compiled in two passes. Both final PDF pages were rendered and visually inspected; no clipping, overlap, missing glyph or unresolved reference was found.

The independent reviewer was a separate AI review process, not an official competition reviewer. No claim of competition acceptance is made.

## Reproduction notes

`build-pdf.sh` assumes an ordinary LaTeX installation. This cloud image contained the standard TeX source/font trees but lacked a configured search index. For the recorded build, TEXINPUTS, TFMFONTS, T1FONTS and TEXFONTMAPS were pointed at their corresponding `/usr/share/texlive/texmf-dist` trees, and TEXFORMATS at an existing locally generated standard pdfLaTeX format. The report source explicitly enables PDF output. No mathematical proof depends on this formatting workaround.

## Eligibility

At the recorded check, upstream main was `6dc8261ea302809ca633aa6c0c903aa8acfacf1f`; metadata marked 00000008196 unsolved. The solution directory returned 404. All-state PR searches for the complete padded identifier, the unpadded identifier and “Staudt” returned zero. The exact read-only responses are retained in `eligibility.json`. Recheck immediately before publication.
