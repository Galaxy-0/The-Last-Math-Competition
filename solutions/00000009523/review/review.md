# Solution Review — Conjecture 00000009523 (PR 725)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005161300`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000009523.md` read in full (bilingual). Shipped `conjecture.md` diffed against it: byte-identical.
- LaTeX: entire `proof.tex` read (206 lines). Independently rebuilt with `latexmk -pdf -interaction=nonstopmode`; build clean. Shipped vs rebuilt PDF compared with pypdf, including a sentence-level prose comparison: all prose sentences match pairwise; the only differences are math-glyph extraction order (bras/kets, sums, subscripts) and hyphenation — cosmetic.
- Lean build: `lake build` succeeds with **zero errors and zero warnings** (8708 jobs; Lean toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360ea` from the prebuilt pool).
- Cheating greps: no `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere in `lean/`.
- Axioms: `Axioms.lean` re-run independently (`lake env lean Axioms.lean`): both `C9523.conjecture9523_false` and `C9523.conjecture9523_false_strong` depend on exactly `[propext, Classical.choice, Quot.sound]`. Matches shipped `verification/axioms.txt`.
- Aux code: no scripts shipped; `verification/` files checked. `axioms.txt` and `build.txt` reproduced/consistent; the two `SHA256SUMS.txt` mismatches (`conjecture.md`, `Basic.lean`) are benign CRLF artifacts — CRLF versions reproduce the recorded hashes exactly, and `conjecture.md` is byte-identical to the official file. Noted.
- Eligibility: `metadata.csv` lists 00000009523 unsolved; no `solutions/00000009523/` on `main`; the PR adds only the 15 files of this submission folder.

## Semantic audit

The conjecture is a conjunction. Its first conjunct says: except for the completely depolarizing constant channel, C_E(phi) > chi(phi) strictly for every channel, where C_E is the Bennett–Shor–Smolin–Thapliyal entanglement-assisted classical capacity C_E(phi) = max_rho I(rho, phi) with I(rho, phi) = S(rho) + S(phi(rho)) − S((id ⊗ phi)(purification)). The submission refutes this conjunct — hence the conjunction — at d = 2; it explicitly does not address the second conjunct (maximal ratio C_E/chi), which is not needed.

The Lean development constructs the real objects, not surrogates: states as PSD trace-one matrices, von Neumann entropy via Mathlib's `Matrix.IsHermitian.eigenvalues` and `Real.negMulLog` (natural log), channels as linear maps that are completely positive for every ancillary dimension k (`idTensor` is the entrywise (id ⊗ phi) on k × n blocks) and trace-preserving, partial trace over the reference factor, and the mutual information exactly as in the BSST formula, with C_E and chi defined as suprema that the submission proves are attained (`IsGreatest`), so the "max" of the conjecture is honored rather than weakened to an unattained sup. The witness is the completely dephasing qubit channel D(X) = diag(X_00, X_11): `deph_isChannel` proves CP via the Kraus form (id ⊗ D)(X) = Σ_a P_a* X P_a with diagonal projectors, and trace preservation; `deph_nonconstant` shows it fixes |0><0| and |1><1|, so it is not a constant channel; `deph_ne_depol` distinguishes it from the completely depolarizing map X ↦ tr(X)/2 · I.

The capacity computations are exact and complete. Key identity (`mutualInfo_deph`): for every purification psi of rho, (id ⊗ D)(|psi><psi|) is block-diagonal with rank-one blocks whose eigenvalues are the block weights tau_a = Σ_r |psi(r,a)|², and D(rho) = diag(tau), so S(D rho) = S((id ⊗ D)(psi)) and I(rho, psi, D) = S(rho) ≤ log 2 for every qubit state (binary entropy bound, Mathlib `binEntropy_le_log_two`), with equality at the Bell state; hence C_E(D) = log 2. For chi, every finite ensemble's Holevo quantity equals H(avg diag) − Σ p_i H(diag_i) ≤ log 2 (entropy concavity plus the binary bound; I re-verified by random search over ensembles, max found 0.6163 < log 2), attained by {1/2|0><0|, 1/2|1><1|}; hence chi(D) = log 2. So C_E(D) = chi(D), and the strict inequality fails for a channel that satisfies every stated hypothesis. The two final theorems negate the clause both literally (only depol 2 excepted) and under the weaker readings where every channel constant on states is excepted and chi > 0 is required — closing the interpretive loophole about "constant channel". The result agrees with the literature (Shirokov: C_E = chi for classical–quantum channels; D is the c-q channel of the computational-basis measurement), which the paper cites as consistency, not as a proof step.

I checked the quantifier structure against the official text: the conjecture's universal claim over channels is negated by one channel on Fin 2 ⇔ ℂ², which the text's "for every channel" admits. No hypotheses are strengthened, nothing is assumed, and the entropy convention (natural log) does not affect the equality C_E = chi.

## Issues found

None blocking. (Minor, noted: two `SHA256SUMS.txt` entries mismatch the committed LF files because the author hashed CRLF copies; content identical modulo line endings.)

## Verdict

APPROVED. A faithful and rigorous disproof of the first conjunct by the canonical counterexample: the dephasing qubit channel is a genuine CPTP, non-constant channel with C_E = chi = log 2, proven from the BSST formula with attained suprema; the negation theorems cover both the literal and the weaker readings of the exception clause. Build clean, axioms standard, report matches the formalization and the known literature.
