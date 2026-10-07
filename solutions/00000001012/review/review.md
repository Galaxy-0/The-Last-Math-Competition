# Solution Review — Conjecture 00000001012 (PR 767)

**Submission:** Jackmeson1 — `solutions/00000001012/Jackmeson1_submission_20261005215027`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (`conjectures/00000001012.md`, English + Chinese); shipped `conjecture.md` copy is **byte-identical** to it (`diff` clean).
- **LaTeX**: entire `proof.tex` (187 lines) read; `latexmk -pdf` rebuild in a scratch dir succeeds. Rebuilt PDF text vs shipped PDF text (pypdf, whitespace-normalized): content matches; differences are glyph-extraction artifacts only (minus signs / braces / `|` extracted as control chars or `f`/`g` in one PDF's OT1 font mapping, `{p}` read as `fpg`, differing Unicode minus) — cosmetic.
- **lake build**: succeeds with **zero errors, zero warnings** on Lean 4.33.1, Mathlib v4.33.1 (rev `0df444a360`, prebuilt pool), 8708 jobs.
- **Axioms**: independent scratch `Check.lean` audit of `Conjecture1012.subdegrees_PSL`, `Conjecture1012.psl_two_transitive`, `Conjecture1012.card_points_one` — each reports exactly `[propext, Classical.choice, Quot.sound]`.
- **No cheating**: grep for `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, declared `axiom`: only hits are the `#print axioms` audit lines in `Axioms.lean`.
- **Aux code**: `verification/axioms.txt` and `verification/build.txt` claims reproduce exactly on a fresh build. SHA256SUMS.txt's single mismatch (`conjecture.md`) is a CRLF-vs-LF line-ending artifact of the Windows authoring environment; content is identical.
- **Metadata**: `metadata.csv` lists 00000001012 with `proven=false`, `completed_by_ai=false` — unsolved before this PR.

## Semantic audit

The conjecture states that the subdegrees of PSL(n,q) acting on the points of PG(n−1,q) are of the explicit (qⁿ−q)/(q−1) type. Subdegrees of a transitive permutation group are the orbit sizes of a point stabilizer; since every transitive action on more than one point has the trivial subdegree 1 (the orbit of the fixed point), the only consistent reading is that the subdegrees are 1 and (qⁿ−q)/(q−1). The submission proves this complete statement and explicitly rejects the reading on which the trivial subdegree also equals the formula (impossible, since (qⁿ−q)/(q−1) ≥ 2 for n ≥ 2 — itself proved in the file, `subdegree_ge_two`).

The decisive theorem `Conjecture1012.subdegrees_PSL` uses the conjecture's own objects: `PSL n F` is Mathlib's `Matrix.ProjectiveSpecialLinearGroup` (genuinely SL(n,F) modulo its centre) and `PG n F` is Mathlib's `Projectivization F (Fin n → F)`, the one-dimensional subspaces of Fⁿ, with the PSL action identified with the SL action via `psl_smul_eq`. For every point `p` it proves: the action is pretransitive and faithful; the set of stabilizer orbits is exactly `{{p}, {p}ᶜ}` with `{p} ≠ {p}ᶜ`; the orbit quotient has cardinality 2; the orbit sizes are 1 and (qⁿ−q)/(q−1) with exact division (q−1)·((qⁿ−q)/(q−1)) = qⁿ−q and (qⁿ−q)/(q−1) = (qⁿ−1)/(q−1) − 1; and the set of subdegree values is exactly {1, (qⁿ−q)/(q−1)} with 1 ≠ (qⁿ−q)/(q−1). The n = 1 degenerate case (PG(0,q) is a single point, no nontrivial subdegree) is proved separately, so the n ≥ 2 hypothesis is shown to be necessary rather than silently strengthening the statement.

The proof structure is sound: the key input, 2-transitivity of SL(n,F) on projective space, is Mathlib's (`Projectivization.specialLinearGroup_is_two_pretransitive`, credited in the report); it passes to PSL because PSL acts through SL. From 2-transitivity, `orbit_stabilizer_of_ne` shows the stabilizer of `p` moves any x ≠ p to any y ≠ p and never moves x ≠ p to p, so the orbits are exactly {p} and its complement. The point count qⁿ = N(q−1)+1 is Mathlib's `Projectivization.card'`, and the arithmetic lemma (`arith`) correctly extracts N ≥ 3, N − 1 = (qⁿ−q)/(q−1) and exact division from truncated natural arithmetic. I verified the numbers independently: for q=3, n=2 the formula gives 3 (PSL(2,3) ≅ A₄ on 4 points has subdegrees 1,3); for q=3, n=3 it gives 12 = 13−1 points of PG(2,3). All correct. No quantifier mismatch, no strengthened hypotheses, no trivialized reading; the "minimal degree" phrase of the Definition line is correctly out of scope of the Conjecture line and is honestly not claimed.

## Issues found

None blocking.

## Verdict

APPROVED. The submission proves the exact subdegree structure {1, (qⁿ−q)/(q−1)} of the natural action of the genuine PSL(n,q) on the genuine PG(n−1,q) for all finite fields and all n ≥ 2 (with the n = 1 case handled), with a clean build, standard axioms only, faithful definitions, and a report that matches the Lean development statement for statement.
