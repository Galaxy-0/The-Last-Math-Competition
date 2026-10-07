# Solution Review — Conjecture 00000001195 (PR 724)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005155512`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000001195.md` read in full (bilingual). Shipped `conjecture.md` diffed against it: byte-identical.
- LaTeX: entire `proof.tex` read (164 lines). Independently rebuilt with `latexmk -pdf -interaction=nonstopmode`; build clean. Shipped vs rebuilt PDF compared with pypdf: content matches; differences are only ligature (`ff`/`fi`/`q`-script) and math-glyph extraction artifacts plus hyphenation — cosmetic.
- Lean build: `lake build` succeeds with **zero errors and zero warnings** (8708 jobs; Lean toolchain `leanprover/lean4:v4.33.1`, Mathlib rev `0df444a360ea` from the prebuilt pool).
- Cheating greps: no `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, or declared `axiom` anywhere in `lean/`. (`decide` is used only for finite enumerations of S_2, Sym^2(Fin 2) and small multiset facts.)
- Axioms: `Axioms.lean` re-run independently (`lake env lean Axioms.lean`): `C1195.conjecture_1195_false` depends on exactly `[propext, Classical.choice, Quot.sound]`. Matches shipped `verification/axioms.txt`.
- Aux code: no scripts shipped; `verification/` files checked. `axioms.txt` and `build.txt` reproduced/consistent; the single `SHA256SUMS.txt` mismatch (`conjecture.md`) is a benign CRLF artifact — the CRLF version of the file reproduces the recorded hash exactly, and the committed file is byte-identical to the official conjecture. Noted.
- Eligibility: `metadata.csv` lists 00000001195 unsolved; no `solutions/00000001195/` on `main`; the PR adds only the 15 files of this submission folder.

## Semantic audit

The conjecture claims <p_lambda, p_mu * p_nu> = z_lambda * delta ("with lexicographic counting"), where the definition line names the inner (Kronecker) product of symmetric functions. The natural reading — p_lambda the power sums, <,> the Hall inner product, * the Kronecker product, z_lambda = prod i^{m_i} m_i!, delta a 0/1 Kronecker delta — is a universally quantified identity over partitions, and a single counterexample refutes it.

The submission proves the counterexample lambda = mu = nu = (2) in full generality. The degree-2 part of the ring of symmetric functions is isomorphic (via the standard restriction map) to the degree-2 part of Q[x_0, x_1]^{S_2}; this is the standard, faithful finite model, and the submission uses Mathlib's own `psumPart`, `hsymmPart`, `msymm` for the p, h, m bases, with `psumPart_two`, `hsymmPart_two`, `hsymmPart_oneOne`, `msymm_two`, `msymm_oneOne` pinning down the concrete polynomials. Rather than trusting one definition of the two bilinear operations, it characterizes them by their defining properties — the Hall inner product by h/m-duality `B(h_lambda, m_mu) = delta_{lambda mu}` (`IsHallInner`, which determines B on the whole degree-2 part since these are bases) and the Kronecker product by Frobenius multiplicativity `ch(phi) * ch(psi) = ch(phi psi)` (`IsKronecker`, which determines K there since ch is onto) — then proves: (a) such structures exist (explicit `B0`, `K0` verified in Lean to satisfy both definitions, so the statement is not vacuous); (b) for EVERY such pair, `hall_p2_p2` gives <p_(2), p_(2)> = 2 = z_(2) and `kron_p2_p2` gives p_(2) * p_(2) = 2 p_(2), hence <p_(2), p_(2) * p_(2)> = 4 = z_(2)^2; (c) 4 ≠ z_(2)·delta for delta ∈ {0, 1}. The decisive theorem `conjecture_1195_false` packages exactly the negation of the conjectured identity at this triple.

The mathematics is correct, and I verified it independently: since p_lambda = z_lambda ch(kappa_lambda) with kappa_lambda the class indicator, and the pointwise product of indicators of distinct conjugacy classes vanishes, p_mu * p_nu = z_mu delta_{mu nu} p_mu, so the true identity is <p_lambda, p_mu * p_nu> = z_lambda^2 delta_{lambda mu} delta_{mu nu}; at (2) this is 4, while the conjecture demands z_(2)·delta ∈ {0, 2}. A numerical evaluation of the explicit B0/K0 in exact rational arithmetic reproduces B0(h_(2), m_(2)) = 1, B0(p_(2), p_(2)) = 2, B0(p_(2), K0(p_(2), p_(2))) = 4. The paper's "Readings not covered" paragraph honestly discloses that the ordinary-product reading of * (under which the analogous formula is true) and non-0/1 readings of "lexicographic counting" are not addressed; the definition line names the Kronecker product, so this scoping is right. The degree-2 specialization is not a toy surrogate: it is the exact homogeneous piece of the genuine symmetric-function ring where the counterexample lives, with the structures characterized intrinsically rather than replaced.

The LaTeX report's formulas, theorem statements and axiom-audit claims agree with the Lean source; the pre-submission review's z_lambda remark (product over distinct part sizes) was correctly incorporated.

## Issues found

None blocking. (Minor, noted: one `SHA256SUMS.txt` entry mismatches the committed LF `conjecture.md` because the author hashed the CRLF copy; content identical modulo line endings.)

## Verdict

APPROVED. A faithful and robust disproof: the counterexample at lambda = mu = nu = (2) is computed for every Hall inner product and every Kronecker product satisfying their characterizing definitions, whose existence is itself proved, so no definitional escape remains; the value 4 = z_(2)^2 contradicts z_(2)·delta for every 0/1 delta. Build clean, axioms standard, report matches the formalization.
