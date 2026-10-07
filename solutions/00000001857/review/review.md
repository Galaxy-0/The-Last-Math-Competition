# Solution Review — Conjecture 00000001857 (PR 729)

**Submission:** Jackmeson1 — `solutions/00000001857/Jackmeson1_submission_20261005170759`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000001857.md` read in full (English + Chinese). Shipped `conjecture.md` is **byte-identical** to the official file.
- LaTeX: full `proof.tex` (187 lines) read. Independently rebuilt with `latexmk -pdf` — succeeds (3 pages). Shipped vs rebuilt text compared with pypdf after normalization: 99.96% character-stream similarity, 5 non-equal blocks, all of them radical-sign (√) glyph extraction artifacts; no content difference.
- Lean build: `lake build` re-run — **Build completed successfully (8708 jobs), zero errors**. Lean 4.33.1, Mathlib v4.33.1 (pool rev 0df444a360).
- Axioms: fresh `lake env lean Check.lean` audit of every decisive theorem (`conjecture1857_false`, `c3On_lt_one`, `c3_eq`, `c3_bounds`, `integral_eq`, `not_tau_asymp`, `not_tau_isBigO`, `not_tau_rpow_tendsto`, `prob_good_le_prob_disconnected`, `not_prob_good_tendsto_one`, `tau_eq_card_edgeSets`) reports exactly `[propext, Classical.choice, Quot.sound]` in all cases. Cheating grep clean (prose hits only).
- Aux code: `verification/build.txt` and `axioms.txt` match fresh reproduction; `SHA256SUMS.txt` verifies except for `conjecture.md` and `lean/Conjecture1857/Basic.lean`, whose recorded digests match their CRLF (pre-normalization) variants exactly — contents verified intact. Non-blocking.
- Metadata: `metadata.csv` lists 00000001857 as `proven=false, disproven=false`; no solution folder on the main branch; README eligibility statement consistent.

## Semantic audit

The conjecture asserts, for the spanning-tree count τ(G) of a random d = 3 regular graph, that τ(G) is asymptotically c₃ⁿ with c₃ = ((√3−1)/2)²·exp(∫ log(3−2cos θ)dθ/4π), that the numerical limit is 1.175…, and that the closed form is computable. The submission refutes both substantive clauses of this conjunction, on the conjecture's own objects.

Faithfulness. The object τ(G) is the real thing: the Lean counts the actual spanning trees of a Mathlib `SimpleGraph` (graphs T ≤ G on the full vertex set that are trees), and additionally proves the edge-subset characterization. The closed form is written with the actual interval integral, `Real.exp` and `√`; the reading of the unspecified integral over a full period [0,2π] (equivalently [−π,π]) is the natural one, and the main bound is proved for every window of length ≤ 4π, covering all stated alternatives. The random model is the genuine uniform distribution on 3-regular simple graphs on `Fin n` (`reg3`, `prob`). No toy surrogates anywhere.

The numerical refutation is exact, not approximate: using the standard identity |e^{iθ}−q|² = q(3−2cos θ) with q = (3+√5)/2 and Mathlib's circle-average theorem for log|z−a|, the Lean proves ∫₀^{2π} log(3−2cos θ)dθ = 2π log q, hence c₃ = (2−√3)/2·(1+√5)/2 ∈ (0.2167, 0.2169) (`integral_eq`, `c3_eq`, `c3_bounds`) — my independent numerical evaluation gives 0.21677545, inside the proved enclosure. Since the conjecture's own formula evaluates to a number below 1, it cannot equal the claimed numerical limit 1.175… (formalized as c₃ ∉ [1.175, 1.176), a faithful reading of a decimal beginning "1.175"). The conjecture is therefore internally inconsistent as written.

The asymptotic refutation is stronger than required: for ANY sequence of connected finite graphs with n → ∞, τ ≥ 1 while c₃ⁿ → 0, so τ/c₃ⁿ → ∞ (`tau_ratio_tendsto_atTop`), τ ≠ O(c₃ⁿ), and τ^{1/n} ↛ c₃ — the three standard readings of "asymptotically c₃ⁿ" all fail, for random 3-regular graphs included (they are connected a.a.s., and even without connectivity the good event {|τ/c₃ⁿ − 1| < ε} for ε ≤ 1 is empty once c₃ⁿ < 1/2; the submission proves P(good) ≤ P(disconnected) and carries a.a.s. connectivity as an explicitly disclosed hypothesis rather than pretending to prove it). Independent sanity check: McKay's theorem gives the true constant 2/√3 ≈ 1.1547 for random cubic graphs, so the conjecture is genuinely false and a disproof is the correct resolution; the submission relies on no literature constant.

The paper states precisely what is and is not refuted (a reading that discards the formula and keeps only "τ ≈ 1.175ⁿ" is declared out of scope) — an honest scope statement that does not weaken the disproof of the conjecture as written.

## Issues found

None blocking. (The probabilistic theorem `not_prob_good_tendsto_one` is conditional on the a.a.s.-connectivity hypothesis, but this is explicitly disclosed and immaterial: the unconditional deterministic refutation `conjecture1857_false` settles the random clause as well. Same cosmetic SHA256SUMS CRLF note as in VERDICT.json.)

## Verdict

APPROVED. A faithful, complete, machine-checked disproof: the conjecture's closed form is proved to evaluate to ≈ 0.2168 (not 1.175…), and its asymptotic clause is refuted unconditionally for every sequence of connected graphs, hence for random 3-regular graphs. Zero build errors, only the standard three axioms, and the submission proves exactly the negation of the conjecture as written.
