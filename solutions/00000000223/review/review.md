# Solution Review — Conjecture 00000000223 (PR 659)

**Submission:** Jackmeson1 — `solutions/00000000223/Jackmeson1_submission_20261005083040`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full (English + Chinese) from `conjectures/00000000223.md`; shipped `conjecture.md` is byte-identical to it (`diff` clean).
- LaTeX read in its entirety; independently rebuilt with `latexmk -pdf -interaction=nonstopmode` (exit 0, 2 pages). Shipped vs rebuilt text compared with pypdf after whitespace normalization: content matches; the only difference is a single spurious glyph inserted by pypdf's ToUnicode mapping of a `q` in one rendering (`Prime i` vs `Prime iQ`) — a cosmetic extraction artifact, not a content difference.
- `lake build` from a clean `.lake` (shipped build artifacts removed; `.lake/packages` symlinked to the prebuilt pool): **Build completed successfully (8708 jobs), 0 errors, 0 warnings**, toolchain `leanprover/lean4:v4.33.1`, Mathlib v4.33.1 rev `0df444a360`.
- `#print axioms` run fresh (`lake env lean AuditCheck.lean`) for `conjecture_223_density_clause_false`, `no_nonzero_density`, `not_exact_form`, `not_asymptotic_form`, `hasNatDensity_divSet`, `not_dvd_euclid`: every one depends only on `propext`, `Classical.choice`, `Quot.sound`. Grep for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/declared `axiom`: only prose hits in README/tex.
- Aux code: `verification/axioms.txt` and `verification/build.txt` match fresh reproduction (same capstone theorem, same success line). Note: `verification/SHA256SUMS.txt` is stale for `conjecture.md` and `lean/Conjecture223/Basic.lean` (12/14 entries OK) — hygiene only; the shipped files are the actual PR contents (re-extracted from `refs/remotes/pr/659` and re-verified from scratch).
- Metadata: `metadata.csv` lists 00000000223 as unsolved; submission adds only its own folder.
- Independent numeric checks: p_n# for n = 6 is 30030, so E_6 = 30031 = 59 · 509, and 59 = p_17 (sixteen primes below 59), so 59 ∣ E_n only possibly for n ≤ 16 — exactly as the report's example states; the counting bound #(D_q ∩ [0,N)) ≤ r+1 gives density 0.

## Semantic audit

The official conjecture is a three-clause conjunction about Euclid numbers E_n = p_n# + 1: (A) the least prime factor of E_n exceeds p_n for all sufficiently large n; (B) least prime factors are uniformly distributed on the logarithmic scale over (p_n, p_n²); (C) for a fixed prime q, the density of n with q ∣ E_n is an explicit value of q^{-2} type. The submission refutes clause (C), which refutes the conjunction, and says so plainly; clauses (A) and (B) are not used (the report notes (A) is in fact true by the same argument and (B) is open).

The disproof is by the classical Euclid argument, proved in Lean rather than assumed: `not_dvd_euclid` shows p_{r+1} ∤ E_n for n > r (p_{r+1} divides p_n#, so it would have to divide 1), `divSet_subset` confines {n : q ∣ E_n} to [0, π(q)], and a squeeze against (r+1)/N → 0 (`hasNatDensity_zero_of_subset`) gives natural density exactly 0 for every prime q. Uniqueness of limits (`density_eq_zero`) then kills every nonzero reading of the clause: the exact form density = c/q² with c ≠ 0 fails already at q = 2 (0 = c/4 forces c = 0), and the asymptotic form q²·d(q) → c ≠ 0 along the primes fails because d(q) = 0 identically makes the limit 0 (`not_asymptotic_form`). The objects are the conjecture's own: `primorialFirst` is the product of the first n primes via `Nat.nth Nat.Prime` (correctly avoiding Mathlib's `primorial`, which multiplies primes ≤ n), `euclid n = primorialFirst n + 1`, and natural density is the standard counting limit. These are genuine infinite statements about divisibility of all Euclid numbers, not a toy surrogate, and no deep theorem is assumed as a hypothesis — the entire content is Euclid's 2300-year-old observation plus a counting bound.

The one judgment point is the reading of "an explicit value of q^{-2} type" ("q^{-2} 型显式值"): the true density 0 = 0 · q^{-2} trivially satisfies a pure O(q^{-2}) bound, which the submission explicitly does not refute and flags for the reviewer. But an "explicit value of q^{-2} type" asserts a value carrying q^{-2} scaling (0 has no q-dependence at all), and under the bound reading the clause would be a contentless truism rather than a stated density value; both contentful readings — exact constant multiple and asymptotic equivalence — are formalized and refuted. The density computation itself was independently verified (E_6 = 30031 = 59 · 509, 59 = p_17, finiteness of D_q). This is an honest, faithful disproof of the conjecture as written.

Build, axioms, conjecture checksum, PDF parity, and aux verification outputs all reproduce; the report and Lean match.

## Issues found

None blocking. Non-blocking note: `verification/SHA256SUMS.txt` is stale for two entries (`conjecture.md`, `lean/Conjecture223/Basic.lean`); both files were re-extracted from the PR branch and independently rebuilt and verified, so no integrity problem remains.

## Verdict

APPROVED. A faithful Lean disproof of the conjecture's density clause on the conjecture's own objects: for every prime q the set {n : q ∣ E_n} is finite by Euclid's argument, hence has natural density 0, refuting both the exact c/q² (c ≠ 0) and the asymptotic q²d(q) → c ≠ 0 readings of "an explicit value of q^{-2} type" and thereby the conjecture; the degenerate upper-bound reading is transparently disclosed, the build is clean with only the standard three axioms, and all verification artifacts reproduce.
