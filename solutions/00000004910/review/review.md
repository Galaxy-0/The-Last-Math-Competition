# Solution Review — Conjecture 00000004910 (PR 712)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005134302`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (EN+CN): there exist two MDPs with identical optimal policies and value functions but different transition structures; separation realized by an explicit construction merging redundant actions. `conjecture.md` byte-identical to the official file.
- LaTeX: independent rebuild exits 0; content matches; extraction artifacts only.
- Lean build: exit 0, 8708 jobs, zero errors/warnings.
- Forbidden content: none.
- Axioms: my independent `CheckJ6.lean`: exactly `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs verified (CRLF manifest artifact only).
- Sanity check: reward ≤ 1 with a reward-1 always-available action gives V* = Σ βᵗ = (1−β)⁻¹; the non-injectivity of M₂'s kernel (P(s,red₁) = P(s,red₂)) and injectivity of M₃'s are immediate.

## Semantic audit
This is a PROOF of an existence claim, and the submission handles the delicate phrase "identical optimal policies" honestly: two MDPs with different action sets cannot literally share policies, so the faithful reading — stated and defended in the tex — is that the optimal policy sets correspond exactly under the explicit merge map: Opt(M₂) = push⁻¹(Opt(M₃)) and Opt(M₃) = push(Opt(M₂)). That correspondence, plus literally equal value functions and genuinely different transition structures, is precisely what the conjecture asks for, and the witness is not a triviality: M₂ genuinely contains two distinct duplicate actions whose identification is the "merging of redundant actions" the conjecture names.

The general engine is substantial: for an MDP with q-fibres of exact duplicates (P(s, g(q a)) = P(s, a), r likewise), the submission defines the merged MDP `quot M g`, the history pushforward `histMap`, the policy lift, and the policy pushforward `push` (the conditional law of the merged action given the merged history, with a fallback at probability-zero histories). The heart is `joint_eq` — a disintegration of the joint law of (merged history, merged action) as the merged history law followed by push π — from which `law_push` (merged history process of π in M equals the history process of push π in M₃, by induction with the duplicate hypothesis), `discValue_push`, `law_lift`/`discValue_lift`, `push_lift` (push ∘ lift = id, so push is onto), `optValue_quot` (equal value functions, both suprema both ways) and the two optimality equivalences follow. All expectations are handled in ENNReal with correct tsum manipulations.

The witness `M₂`/`M₃` instantiates everything, and the capstone `conjecture4910` packages the full conjunction: duplicates in M₂; M₃ = quot M₂ rep by `rfl`; non-injective vs injective kernels; equal value functions for every s and β, in the closed form (1−β)⁻¹ attained by the always-opt policy; the law/value preservation and onto statements; the two optimal-set identities for every β; and nonemptiness. The tex also documents (and justifies dropping) an earlier, weaker reading. Values in [0,∞] with the β ≥ 1 convention are handled without hiding the degenerate case.

## Issues found
- None blocking.

## Verdict
APPROVED. A real (not numeral-level) proof of the existence claim: a general merging theorem for MDPs with duplicate actions proved from the definitions of histories, policies and discounted values, instantiated by an explicit two-state witness with genuinely different transition structures, equal value functions and exactly corresponding optimal policy sets.
