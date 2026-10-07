# Solution Review — Conjecture 00000000591 (PR 714)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005134756`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (EN+CN): Wilf e·n(S) ≥ g(S)+e (g = Frobenius number); new-direction claim: on embedding-dimension-3 semigroups (e·n − g − e)/g → 0 with an explicit rate. `conjecture.md` byte-identical to the official file.
- LaTeX: independent rebuild exits 0; content matches; extraction artifacts only.
- Lean build: exit 0, 8708 jobs, zero errors/warnings.
- Forbidden content: none.
- Axioms: my independent `CheckJ6.lean` over all 11 theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs verified (CRLF manifest artifact only).
- Sanity check: ⟨6,10,15⟩ has F = 29, nongaps = genus = 15, surplus 13, ratio 0.448; ⟨6,22,33⟩: F = 71, n = genus = 36, surplus 34, ratio 0.479; k = 2, 5 likewise; ratio → 1/2. All match the Lean statements; F is a gap and all > F lie in S_k (checked up to k = 8).

## Semantic audit
The claim is a limit statement over the class of embedding-dimension-3 numerical semigroups, and the submission defeats it with a single family whose members have unbounded Frobenius number and surplus ratio bounded below by 1/3. The formalization is exactly the written claim: `RatioTendsToZero` = ∀ ε > 0 ∃ N, ∀ S numerical semigroup with embeddingDim = 3, ∀ F with Mathlib's `FrobeniusNumber F S`, N ≤ F → |surplus S F / F| < ε, where surplus, nongaps (elements of S below F), genus, minimal generators (atoms) and embedding dimension are all defined on the actual `AddSubmonoid ℕ` objects, not on a hand-modeled surrogate. This addresses precisely the deficiency the earlier rejections (PRs #132, #169) cited: `mem_S_iff` is a full Apery-set characterization proved for every k by closure induction (36 residue cases for monotonicity) plus explicit witnesses for the forward direction.

From `mem_S_iff` everything follows for every k: the largest gap is 42k+29 (≡ 5 mod 6, below w₅ = 7m = 42k+35, with everything beyond it in S_k), so `frob_S` gives Mathlib's FrobeniusNumber; the atoms are exactly {6, 12k+10, 18k+15} (`minimalGenerators_S`: each generator is not a sum of two nonzero elements since elements below 3m are ≡ 0, 4 mod 6; every other element splits off a generator), so `embeddingDim_S = 3`; the involution x ↦ F−x swaps elements and gaps in [0, F] (`P_symm`), so genus = nongaps = 21k+15; surplus = 3(21k+15) − (42k+29) − 3 = 21k+13 ≥ (42k+29)/3. The main theorems `not_ratioTendsToZero` and `not_genusRatioTendsToZero` are the exact negations of the two readings of "g" (the official text defines g as the Frobenius number; the genus reading is refuted in parallel with ratio ≥ 1), witnessed at S_N with the formal hypotheses all discharged.

I verified the family numerically (k = 0, 1, 2, 5): every stated value matches, and the ratio (21k+13)/(42k+29) → 1/2, decisively away from 0. The refutation is robust: no reading of "explicit convergence rate" survives the failure of the limit itself.

## Issues found
- None blocking.

## Verdict
APPROVED. A genuine, fully general Apery-set formalization of the counterexample family ⟨6, 2(6k+5), 3(6k+5)⟩ proving every quantity the conjecture's negation needs, for all k, on the actual submonoid objects — exactly what earlier reviews demanded — with clean build, standard axioms only, and numerics that confirm the Lean statements.
