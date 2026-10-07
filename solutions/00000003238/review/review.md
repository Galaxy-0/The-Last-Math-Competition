# Solution Review — Conjecture 00000003238 (PR 823)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261006165718`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Conjecture read in full (bilingual) from `conjectures/00000003238.md`; shipped `conjecture.md` is byte-identical to it (`diff` clean).
- LaTeX: full `.tex` read; `latexmk -pdf -interaction=nonstopmode` rebuild in a scratch dir succeeds with 0 errors. Shipped vs rebuilt PDF text compared with pypdf: word-for-word identical; all differences are glyph-mapping extraction artifacts (⊕, ∪, ∑, ≤, ∈ extracted with different Unicode mappings by the author's TeX) and math spacing. Cosmetic.
- Lean build: `lake build` from scratch against the prebuilt pool, 0 errors, 0 warnings (Lean 4.33.1, Mathlib v4.33.1, rev 0df444a360 pinned identically by `lake-manifest.json`).
- Axioms: `#print axioms` re-run independently for `not_edgeTheorem`, `edge_theorem_counterexample`, `spectrum_T`, `spectrum_shift`, `mem_spectrum_T`, `dsum_unique` — all report exactly `propext, Classical.choice, Quot.sound`. Grep for cheating markers: only audit prose hits.
- Aux code: fresh `Axioms.lean` output matches the claims; all 14 entries of `verification/SHA256SUMS.txt` reproduce over the shipped files (the two "mismatches" are pure CRLF/LF artifacts; CRLF-normalized hashes match exactly).
- Metadata: `metadata.csv` lists 00000003238 as `proven=false, disproven=false` (unsolved); no competing solution folder.

## Semantic audit

The conjecture's main clause is the "edge theorem" identity: the closure of the spectrum of a direct sum of operators equals the union-closure of the block spectra (the trailing "accumulated edges" clause uses an undefined term and is joined by "with"/"and"; refuting the equality suffices to refute the conjunction). As stated there is no finiteness or normality hypothesis — "a direct sum of operators" with a "family of summands" and "limit points", i.e. the infinite-family reading, which is the only reading under which the clause has content (for finite direct sums the identity is trivially true, and the submission says so explicitly).

The submission proves `¬EdgeTheorem` by explicit counterexample: T = ⊕_n J_n, the direct sum over n of the nilpotent Jordan shift J_n on ℂ^{n+1}, on Mathlib's Hilbert sum `lp Block 2`. Lean proves `dsum` is the unique bounded blockwise operator with ‖T‖ ≤ 1; `spectrum_shift`: σ(J_n) = {0} (unit + commuting nilpotent is a unit; nilpotent in a nontrivial ring is not), so closure(⋃_n σ(J_n)) = {0}; and `spectrum_T`: σ(T) is exactly the closed unit disc. The upper bound is Mathlib's spectral-radius inclusion; the lower bound is the classical test-vector argument: (z·1 − J_n)(1, z, …, zⁿ) = z^{n+1}e_n with the test vector of norm ≥ 1, so a bounded inverse S of z·1 − T would force 1 ≤ ‖S‖·|z|^{n+1} for all n — contradiction for |z| < 1 — and σ(T) closed gives the closed disc. Hence 1/2 ∈ σ(T) \ {0} = closure(σ(T)) \ closure(⋃σ(J_n)).

The formalization is faithful. Mathlib's `spectrum ℂ` in the Banach algebra of bounded operators and the standard Hilbert (ℓ²) direct sum are exactly the conjecture's objects; the counterexample is a genuine uniformly bounded (indeed contractive) family of genuine operators, instantiating the universal statement. This is not a toy surrogate: the resolvent-blowup mechanism by which points of the disc enter σ(T) although no block sees them is precisely the phenomenon the "accumulated edges" phrase gestures at, and the conjecture's naive union-closure identity is genuinely false for it. I verified the mathematics numerically: all eigenvalues of J_n are 0, the test-vector identity holds, ‖(z·1 − J_n)⁻¹‖ ≥ |z|^{−(n+1)} (n ≤ 25), and σ_min(z·1 − J_n) → 0, so z − T is not bounded below on the infinite sum. The submission's "readings not refuted" section (finite sums, normal families) is accurate and does not weaken the disproof, since the text states neither restriction.

## Issues found

None blocking. Non-blocking notes:
- Shipped `verification/axioms.txt` lists only `not_edgeTheorem` and `spectrum_T`, while the report's audit paragraph names five theorems. I re-ran the audit for all five (plus one) myself: all clean, so the report's claim is true; the shipped file is just a subset.
- `verification/SHA256SUMS.txt` was computed over CRLF versions of `conjecture.md` and `lean/Conjecture3238/Basic.lean`; shipped files are the LF archive renders, content otherwise byte-identical.

## Verdict

APPROVED. A complete, faithful, machine-checked disproof: the infinite direct sum of nilpotent Jordan blocks has spectrum the closed unit disc while every block has spectrum {0}, so the conjectured union-closure identity fails for a contractive family of operators on Hilbert spaces — well inside the conjecture's stated scope, with the classical mechanism made fully explicit. Build clean, axioms clean, LaTeX/PDF consistent, shipped conjecture copy verbatim.
