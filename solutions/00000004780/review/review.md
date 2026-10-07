# Solution Review — Conjecture 00000004780 (PR 647)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005073351`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — two matrix models with identical joint-moment asymptotics but different operator-valued distributions, separated by an explicit block-structure rearrangement; `conjecture.md` is byte-identical to `conjectures/00000004780.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt (exit 0); shipped/rebuilt text matches up to glyph extraction artifacts.
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: none executable; no `sorry`, no `native_decide`, no axiom declarations.
- Axioms: independent run — `Conjecture4780.conjecture4780`, `rearrange_jointMoment`, `rearrange_condExp`, `rearrange_bMoment_first` all use only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: the trace identities tr_{2N}(M⊗1_N) = tr₂(M) and E_N(PMP⁻¹) = σE_N(M)σ⁻¹ were re-derived by hand.

## Semantic audit
The conjecture is an existence statement with an explicit-rearrangement clause, and the submission proves it with fully computed witnesses. The definitions are the standard noncommutative-probability ones: a matrix model is a sequence of r-tuples in M₂(M_N(ℂ)) ≅ M_{2N}(ℂ); joint moments are normalized traces φ_N(p) = tr_{2N}(p(X_N)) with p ranging over the free algebra (evaluated by `FreeAlgebra.lift`, so quantification over all noncommutative polynomials is genuine); the B = M₂(ℂ)-valued structure is given by the left embedding b ↦ b⊗1_N and the block conditional expectation E_N = id₂⊗tr_N, and the B-valued distribution consists of the moments E_N(b₀X_{i₁}b₁⋯X_{i_m}b_m). Nothing is assumed by fiat: E_N is computed entrywise, and the moment that separates the models is actually evaluated.

The two half-proofs are both genuine. First, a block permutation P_σ induces an algebra automorphism M ↦ P_σMP_σ⁻¹ (Mathlib's reindex algebra equivalence), so by the universal property p(P_σXP_σ⁻¹) = P_σp(X)P_σ⁻¹ and the normalized trace is invariant under reindexing; hence φ_N^Y(p) = φ_N^X(p) for every N and every p — identical for all N, which gives identical asymptotics under any reading — and Lean also proves the common limit tr₂(p(A,C)) exists (the sequence is eventually constant since p(X_N) = p(A,C)⊗1_N and tr_{2N}(M⊗1_N) = tr₂(M)). Second, E_N(X_{N,1}) = E_N(A⊗1_N) = A = diag(1,0) by entrywise computation, while the same first B-valued moment of Y is σAσ⁻¹ = diag(0,1) (`rearrange_condExp`), so the B-valued distributions differ for every N ≥ 1 and their limits differ as well. The first B-valued moment belongs to every reasonable version of the operator-valued distribution, so no weaker notion escapes the separation.

The second model is literally the first with its two diagonal blocks swapped — an explicit rearrangement of the block structure as demanded. The models are deterministic and of the form a⊗1_N; the conjecture imposes neither randomness nor an ensemble, and the report says so transparently. Nothing is strengthened, weakened, or trivialized.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hash of `conjecture.md` does not match the shipped file; the shipped copy is byte-identical to the official source).

## Verdict
APPROVED. A correct, faithfully formalized existence proof with explicit, computed witnesses; all audited checks reproduce.
