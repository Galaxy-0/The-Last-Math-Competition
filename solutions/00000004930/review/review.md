# Solution Review — Conjecture 00000004930 (PR 648)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005073703`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read: yes — two MDPs with identical values for all discount factors but different average rewards, separated by a construction concentrating discount weights on transients; `conjecture.md` is byte-identical to `conjectures/00000004930.md`.
- Change scope: only the submission folder was added.
- LaTeX: independently rebuilt (exit 0); shipped/rebuilt text matches up to glyph extraction artifacts.
- Lean build: `lake build` exit 0, zero errors, zero warnings.
- Forbidden content: none executable; no `sorry`, no `native_decide`, no axiom declarations.
- Axioms: independent run — `Conjecture4930.conjecture4930` uses only `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs reproduce; SHA-256 manifest stale (see Issues).
- Semantic audit: pass (below).
- Independent arithmetic check: the countdown timing (playing n rewards times 0..n+1), the tail bound E[r_{t+1}] ≤ Σ_k q(k+t), and Cesaro's argument were re-derived by hand.

## Semantic audit
The conjecture is an existence statement with an explicit-construction clause, and the submission proves it. The formalization is the standard countable-state MDP model: `MDP` with state/action types, initial state, transition laws in `PMF`, nonnegative rewards; policies are fully history-dependent and randomized (`Hist M → PMF (Act M)`), so no policy-class shortcut is taken; the discounted value is the ℓ¹-style series Σ_t β^t·E[r(s_t,a_t)] in `[0,∞]` and the optimal value is the supremum over policies; the average reward is the limit of T-step averages, with `toReal` on expected rewards justified since both witnesses have rewards in {0,1} (proved ≤ 1 in Lean). β ranges over all of `[0,∞]`, stronger than the β ∈ [0,1) reading.

The two witnesses are explicit and non-degenerate. MDP A is the trivial reward-1 process: every policy has expected reward 1 forever, V* = (1−β)⁻¹, average reward 1. MDP B concentrates all reward on transients: from start the chosen n determines the countdown length; states count(n),…,count(0) pay 1, the sink pays 0, and every state is visited at most once — exactly "concentrating the discount weights on transients". The value equality is proved from both sides: V ≤ (1−β)⁻¹ by the reward bound, and the deterministic policy playing n achieves Σ_{t≤n+1}β^t, so V* ≥ sup_n Σ_{t<n}(β^t) = (1−β)⁻¹. For the average, `law_state` (induction on t) shows that after the first action the state law is the pushforward of the first-action distribution under the fixed countdown map — the post-start actions are genuinely irrelevant since the transition function there ignores them — hence E[r_{t+1}] is at most the tail of a probability mass function and tends to 0; Cesaro averaging (formalized) gives average reward 0 under every policy. Thus optimal average rewards differ (1 vs 0), and every lim/liminf/limsup variant agrees because the limits exist for all policies.

The report correctly notes the separation is impossible for finite MDPs (Blackwell's g* = lim (1−β)V*_β) and for a single fixed policy (the generating function determines the reward sequence); the conjecture restricts neither, so the witnesses are within scope. Nothing is trivialized: the discounted criterion genuinely sees the transient rewards and the average criterion genuinely does not.

## Issues found
- Non-blocking: `verification/SHA256SUMS.txt` is stale (hash of `conjecture.md` does not match the shipped file; the shipped copy is byte-identical to the official source).

## Verdict
APPROVED. A correct, faithfully formalized existence proof with explicit witnesses of the advertised shape; all audited checks reproduce.
