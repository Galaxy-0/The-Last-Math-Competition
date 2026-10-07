# Solution Review — Conjecture 00000008189 (PR 660)

**Submission:** Jackmeson1 — `solutions/00000008189/Jackmeson1_submission_20261005083351`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full (English + Chinese) from `conjectures/00000008189.md`; shipped `conjecture.md` is byte-identical to it (`diff` clean).
- LaTeX read in its entirety; independently rebuilt with `latexmk -pdf -interaction=nonstopmode` (exit 0, 2 pages). Shipped vs rebuilt text compared with pypdf, whitespace-normalized: **identical** (3105 word-characters); the raw diff shows only spacing artifacts from different TeX font subsetting.
- `lake build` from a clean `.lake` (shipped build artifacts removed; `.lake/packages` symlinked to the prebuilt pool): **Build completed successfully (8708 jobs), 0 errors, 0 warnings**, toolchain `leanprover/lean4:v4.33.1`, Mathlib v4.33.1 rev `0df444a360`.
- `#print axioms` run fresh (`lake env lean AuditCheck.lean`) for `conjecture_8189_false`, `halfPoisson_contradicts_largeIndex`, `tail_ne`, `ratio_sum`, `card_partition`: every one depends only on `propext`, `Classical.choice`, `Quot.sound`. Grep for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/declared `axiom`: only prose hits in README/tex.
- Aux code: `verification/axioms.txt` and `verification/build.txt` match fresh reproduction (same theorem names, same success line). Note: `verification/SHA256SUMS.txt` is stale for `conjecture.md` and `lean/Conjecture8189/Basic.lean` (12/14 entries OK) — a hygiene issue only; the shipped files are the actual PR contents (re-extracted from `refs/remotes/pr/660` and re-verified from scratch).
- Metadata: `metadata.csv` lists 00000008189 as unsolved; submission adds only its own folder.
- Independent numeric checks: Poisson(1/2) masses at k = 0, 1, 2 are 0.606531, 0.303265, 0.075816 (sum 13/8 · e^{-1/2} ≈ 0.985612); forced tail density 1 − (13/8)e^{-1/2} ≈ 0.014388 vs the stated e^{-1/2}/48 ≈ 0.012636; equality forces e = 6241/2304 ≈ 2.708767 < 2.71 < e ≈ 2.718282. All confirm the report.

## Semantic audit

The official conjecture (both languages) makes four claims: (A) the density of irregular primes is 1 − e^{-1/2}; (B) the irregularity index i(p) — the number of irregular pairs (p, k) — is Poisson(1/2) distributed; (C) the density of primes with index at least 3 is e^{-1/2}(1/2)^3/3!; (D) an expected count of 0.00 Vandiver counterexamples in extending the verified threshold from 10^9 to 10^11. The submission proves the negation of (A) ∧ (B) ∧ (C), which implies the negation of the full four-clause conjecture: an exact disproof.

The inconsistency is real and is exhibited honestly. The Lean development defines the conjecture's own objects: `irregIndex p` counts even k with 2 ≤ k ≤ p−3 and p ∣ (Mathlib `bernoulli k).num` (the standard irregularity index; the B_1 sign convention is irrelevant for even k ≥ 2), `HasPrimeDensity` is relative natural density among the primes, and the Poisson(1/2) law uses Mathlib's `poissonMeasure` with `poissonMeasure_real_singleton` giving e^{-1/2}(1/2)^k/k!. The proof first shows the four index classes {0}, {1}, {2}, {≥3} partition the primes, so their counting ratios sum to 1 for every X ≥ 2 (`card_partition`, `ratio_sum`); then, if (B) and (C) give the four limiting densities, uniqueness of limits forces Poisson{0}+Poisson{1}+Poisson{2}+e^{-1/2}/48 = 1, i.e. e^{-1/2} = 48/79, i.e. e = 6241/2304 ≈ 2.7088 — contradicting Mathlib's rigorous bound `exp_one_gt_d9` (e > 2.7182818283). Nothing about Bernoulli numbers is assumed or needed: the refutation uses only finite additivity and normalization on the actual prime counts, which is exactly why it is decisive. The unformalized clause (D) is meta-statistical and its omission is immaterial, since refuting (B) ∧ (C) already refutes the conjecture as a whole.

The only reading under which the conjecture survives is if "(at least 3)"/"≥ 3" were a slip for "exactly 3", in which case (C) would be the k = 3 case of (B). The submission does not adopt that amendment: both the English and Chinese texts say at least 3, and it explicitly documents the unrefuted amended reading for the reviewer. That is the faithful choice. All arithmetic was independently verified numerically.

Build, axioms, conjecture checksum, PDF parity, and aux verification outputs all reproduce; the report and Lean match.

## Issues found

None blocking. Non-blocking note: `verification/SHA256SUMS.txt` is stale for two entries (`conjecture.md`, `lean/Conjecture8189/Basic.lean`); both files were re-extracted from the PR branch and independently rebuilt and verified, so no integrity problem remains.

## Verdict

APPROVED. A faithful, self-contained disproof: the conjecture's own Poisson(1/2) clause and its "at least 3" density clause are jointly contradictory by finite additivity alone (forced tail 1 − (13/8)e^{-1/2} ≈ 0.014388 versus the stated e^{-1/2}/48 ≈ 0.012636; agreement would give e = 6241/2304 < 2.71), the formalization uses the real objects with exact quantifiers, the build is clean with only the standard three axioms, and every shipped verification artifact reproduces.
