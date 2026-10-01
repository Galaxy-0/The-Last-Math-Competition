# Independent semantic review — TLMC 00000002320

Reviewer: sibling task `/root/triage_b`, which did not author the 2320 proof.
Review date: 2026-09-21 Asia/Shanghai.

Verdict: **semantic alignment passes for the necessary interval consequence**. The argument supplies an actual finite group, the standard generated-subgroup relation, and the standard finite probability. This review is separate from compilation, axiom audit, kernel replay, and organizer review. It does not certify any of those checks.

## Material reviewed

- Both English and Chinese organizer statements in `upstream/conjectures/00000002320.md`, at pinned organizer commit `95acb520ec5607c826b8a997b1ef2fc82d6f7c57`.
- `lean/Results/Counterexample2320.lean`, final reread SHA-256 `537b22be799a0cbd9ef5e93be9ab762e976d016d0901349c4147b188a60a342d`.
- `rounds/20260921/problem2320_math.md`, SHA-256 `3b73ba06a47b5d06796bd23e63411d822e1f7ac45c09fe4634a701b856cc6a51`.
- Mathlib's documentation of `Multiplicative`, which transports additive structure to multiplicative notation.
- Igor Pak, *On probability of generating a finite group*, 30 December 1999, Section 1, printed page 3. The author-hosted source was opened directly: <https://www.math.ucla.edu/~pak/papers/sim.pdf>. It defines the probability for uniform independent k-tuples as their generating-tuple count divided by the kth power of the group order, matching the implementation at k=2.

## Statement and hypotheses

Both source languages quantify over **all finite groups**. Neither adds simplicity, nonabelianness, nor two-generation. The elementary abelian group of order eight therefore satisfies the advertised scope; excluding it would change the original statement.

If a spectrum is a subsequence of `[1/4,1]`, every member must lie in that interval. It is sufficient to refute this membership consequence at one group; the density claim and the independent PSL(2,p) asymptotic assertion need not be formalized to do so. The explanatory note states this restriction accurately.

## Mathematical-to-formal bridge

1. `Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)` is an actual mathlib group representing coordinatewise addition on `(Z/2Z)^3`; it is not a custom toy predicate standing in for groups.
2. `fourSubgroup` has the proposed carrier `{1,a,b,a*b}` and is supplied with actual identity, multiplication, and inverse closure proofs. Even when entries coincide, this remains a subgroup of at most four elements.
3. `four_misses_element` states that every such subgroup omits an actual group element. Together with the proved cardinality eight, this matches the elementary rank obstruction.
4. `pair_closure_le_four` uses actual `Subgroup.closure` of the set `{a,b}`. The inclusion of both generators is explicit. Thus `no_pair_generates` addresses standard group generation.
5. `generatingPairs` ranges over all ordered pairs and tests exactly whether their generated subgroup is top. Its cardinality, rather than a surrogate score, is used in `generatingPairProbability`.
6. The denominator is the square of the group order; the count is zero for this group. Working in exact rationals gives the same zero probability and interval contradiction as the usual real-valued probability. No approximate computation is involved.
7. `decide` is used for finite decidable facts. There is no `native_decide`, custom axiom, assumed subgroup-generation lemma, or external numerical result in the reviewed source. Kernel acceptance and final axiom dependencies must still be checked by the coordinator.

## Findings and limits

No semantic defect requiring a source change was found. The representation as rational probability is transparent and mathematically adequate for this counterexample. Restricting the formal universal predicate to types in `Type` is also adequate to refute the unrestricted claim, because the exhibited finite group is among those types.

This is an elementary established obstruction applied to a generated conjecture, not a new group-theoretic discovery. The bounded PR-title/body check does not establish originality or organizer acceptance. Keep those limits in the final report and submission notes.

The initial reviewed source hash was `7a2ff8b5e0694d1b8b14f1b872a991690b70369b3d8f7563ca01515a99452d5c`. After its compiler repairs, the reviewer reread the complete final source at the hash listed above. The changes add the explicit decidability instance, supply subgroup proof arguments, adapt the closure API, and expose subgroup membership to the elaborator. They preserve the group, generation predicate, probability definition, hypotheses, and theorem statements; the semantic verdict remains unchanged.

This verdict applies to the final hashes above. If later edits change definitions, hypotheses, or theorem statements, review the changed portions again. Tactical repairs that preserve those statements require final compiler/kernel verification but do not themselves change the semantic conclusion.
