# Solution Review — Conjecture 00000006120 (PR 649)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005074010`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — two Boolean functions with identical (all-ρ) noise stability but different spectral distributions, and a realizing pair with the same stability but different low-degree weights; `conjecture.md` is byte-identical to `conjectures/00000006120.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt (exit 0); shipped/rebuilt text matches up to glyph extraction artifacts (the shipped PDF extracts ∑/± correctly; the rebuilt one maps them differently — purely an extraction artifact).
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: none executable; no `sorry`, no `native_decide`, no axiom declarations.
- Axioms: independent run — `conjecture6120_false`, `no_realizing_pair`, `noiseKernel_sum` use only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent check: the kernel expansion ½(1+ρx_iy_i), the polynomial identity and its coefficient comparison were re-derived by hand.

## Semantic audit
The conjecture is a conjunction: (A) two Boolean functions with identical noise stability, (B) different spectral distributions, (C) the separation realized by an explicit pair with the same stability but different low-degree weights. The submission proves (C) is unsatisfiable, hence the conjunction false, and proves (A)+(B) satisfiable (two dictators on {−1,1}²: equal stability for every ρ, different spectral distributions since one has weight on {0} and the other not) so the development is non-vacuous — the definitions are the standard O'Donnell ones (χ_S, f̂(S) = 2⁻ⁿΣ f(x)χ_S(x), spectral distribution S ↦ f̂(S)², noise kernel, W^k and W^{≤k}).

The heart is the polynomial identity, proved in Lean from the probabilistic definition: the kernel entry factors as ½(1+ρx_iy_i), so K_ρ(x,y) = 2⁻ⁿ Σ_S ρ^{|S|}χ_S(x)χ_S(y) and Stab_ρ[f] = Σ_S ρ^{|S|}f̂(S)²; Lean packages this as a real polynomial `stabPoly f` with `eval ρ = stab ρ f` and `coeff k = weight f k`. Consequently `weight_eq_of_stab_eq`: if Stab_ρ[f] = Stab_ρ[g] on any infinite set of ρ (Lean uses [0,1], strictly weaker than the [−1,1] of "identical noise stability", and any n, m are allowed), then P_f = P_g by `Polynomial.eq_of_infinite_eval_eq`, so W^k[f] = W^k[g] for all k, and summing gives W^{≤k}[f] = W^{≤k}[g]. `RealizingPair` (same stability on [0,1] plus some differing W^k or W^{≤k}) is therefore empty (`no_realizing_pair`), and `Statement` — the faithful encoding of the full conjecture with an optional separate realizing pair — is negated.

On the reading: "different low-degree weights" is the standard aggregate terminology (O'Donnell's W^{≤k}), and it is the only reading under which clause (C) says something beyond clause (B); under it the clause is mathematically impossible, as proved. The alternative reading (individual coefficients f̂(S)²) under which the conjecture would hold (e.g. the dictators) is explicitly disclosed in the report's scope section rather than hidden. The disproof is exact, quantifier-faithful, and non-degenerate.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hash of `conjecture.md` does not match the shipped file; the shipped copy is byte-identical to the official source).

## Verdict
APPROVED. The realizing clause is provably unsatisfiable under the standard reading of low-degree weights, the formalization is faithful and complete, and all audited checks reproduce.
