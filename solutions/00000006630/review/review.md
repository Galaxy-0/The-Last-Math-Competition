# Solution Review — Conjecture 00000006630 (PR 642)

**Submission:** Jackmeson1 — `solutions/00000006630/Jackmeson1_submission_20261005071950`
**Head:** `d6ca2d111c4f19a3597f2556cad69fc4f2074718`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06
**Result:** Approved

## Checklist results

- Official conjecture (`conjectures/00000006630.md`, English + Chinese) read in full; the submission's `conjecture.md` is byte-identical to it. Source-md check: pass.
- LaTeX report read in its entirety; independent `latexmk -pdf` rebuild succeeded; extracted text of shipped and rebuilt PDFs matches modulo standard glyph/ligature extraction artifacts (`ffi`/`fi`/`all` ligatures, math-glyph mapping). PDF-match check: pass.
- `lake build` (Lean v4.33.1, Mathlib v4.33.1) exits 0 with zero errors and zero warnings. Lean-build check: pass.
- No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. `#print axioms Submission00000006630.conjecture6630` → `[propext, Classical.choice, Quot.sound]` only, independently re-run via the shipped `Axioms.lean`. Axiom check: pass.
- Auxiliary `verification/` material agrees with independently reproduced results; two SHA256SUMS entries (`conjecture.md`, `lean/Conjecture6630/Basic.lean`) hash CRLF newline variants — bookkeeping artifact, content identical. Aux check: pass.
- Semantic audit: pass (details below).

## Semantic audit

The conjecture asks for two lattice-gas models with identical inequalities but different equilibria, the separation realized by an explicit violation with the same inequalities but different configuration counting. The decisive Lean theorem `conjecture6630` realizes every clause with the explicit pair `K2(1)`, `K2(2)` (hard-core gas on two adjacent sites, activities 1 and 2): `profile M₁ = profile M₂` (equality of the full SignType-valued profile functions, not a sample), `gibbs M₁ ≠ gibbs M₂`, the same explicit FKG/Harris violation `<n₀n₁> < <n₀><n₁>` proved in both models, `Z M₁ = 3 ∧ Z M₂ = 5`, and the literal-count bridging lemmas `card_internal_one/two` and `gibbs_eq_count_one/two`. No hypothesis was strengthened; the reading (grand-canonical hard-core exclusion gas, Gibbs equilibrium, correlation-inequality sign profile of occupation monomials) is the standard one for the bilingual text.

I rederived the mathematics. Allowed configurations on two adjacent sites are `∅, {0}, {1}`, so `Z = 1 + 2λ`; `μ({0}) = λ/(1+2λ)`, giving 1/3 vs 2/5. The profile computation reduces (Lemma `profile_eq`, after `n_B n_C = n_{B∪C}`) to the sign of `Z·W(B∪C) − W(B)W(C)`; checking the 16 pairs gives 0 unless `B, C` are nontrivial singleton-class sets, then +1 for `B = C` (e.g. `(1+2λ)λ − λ² = λ + λ² > 0`) and −1 for `{0},{1}` (`−λ² < 0`) — independent of the activity, hence `profile_K2_eq`. The common violation at the adjacent pair is the classical repulsive FKG failure of the hard-core gas. The report's Scope section states exactly which readings are and are not covered; nothing is overstated.

The "different configuration counting" clause deserves note: the partition functions 3 and 5 are proved to be literal configuration counts when each particle carries `q = 1, resp. 2` internal states (maps `Fin 2 → Option (Fin q)` with at most one occupied site, cardinalities 3 and 5 proved by `decide`), and the Gibbs state is proved to be the occupation marginal of the uniform law on those configurations. This makes the count difference fully concrete rather than merely a weighted-sum difference. Faithful and even stronger than required.

Build hygiene: zero errors/warnings; the axiom profile is the allowed minimum, replayed independently. The report lists exactly the Lean declarations that exist and match.

## Issues found

- Minor: two entries of `verification/SHA256SUMS.txt` hash CRLF newline variants of `conjecture.md` and `lean/Conjecture6630/Basic.lean` (verified by re-hashing after newline normalization). Non-blocking hygiene issue.

## Verdict

APPROVED. A correct, fully machine-checked constructive proof with identical inequality profiles, genuinely different equilibria, the same explicit correlation-inequality violation, and concretely different configuration counts; the report faithfully mirrors the Lean development.
