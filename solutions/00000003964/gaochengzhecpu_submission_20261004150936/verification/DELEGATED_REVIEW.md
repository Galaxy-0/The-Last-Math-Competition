# Delegated internal review of conjecture 00000003964

Verdict: **PASS for the disproof of the source as written.** No blocking mathematical or formalization defect was found.

Reviewer: a distinct delegated agent in the same authoring workflow. This is an internal division of work, not an external peer review.

Reviewed on 2026-10-04:

- `SOURCE.md`, `main.tex`, `README.md`, and the complete `lean/Main.lean`.
- Main.lean SHA-256: `e753b9401653d0f1c1ff6f522fb407c29b6eb9f67cd6f2e8e4424ff3dfa10b21`.
- SOURCE.md SHA-256: `4a8cbb21cba0499c8ba29015432535426d07fc44c74c0e148a8dd63a409c969d`, matching the raw source snapshot.
- Relevant pinned Mathlib definitions and proofs in `GroupTheory/SpecificGroups/Cyclic.lean`, `Combinatorics/SimpleGraph/Circulant.lean`, and `Combinatorics/SimpleGraph/Metric.lean`.
- The actual `lean-axioms.log`: all ten printed theorem lists use only `propext`, `Classical.choice`, and `Quot.sound`.

## Adversarial checks

1. **Simple group, rather than an asserted label.** `G` is the actual additive group `ZMod 1021`. The local `Fact (Nat.Prime 1021)` is proved by kernel-checked `norm_num`, not introduced as an axiom. The imported `ZMod.instIsSimpleAddGroup` derives simplicity from the cyclic prime-order classification. The source says every finite simple group in both languages and has no nonabelian restriction. Prime cyclic groups therefore qualify. Both prose files explicitly preserve this scope and disclaim a nonabelian-only variant.

2. **Actual generators and Cayley graph.** `generator_generates` proves the actual additive-subgroup closure of `{1}` is top: each residue is its natural representative times 1. The graph is `cycleGraph 1021`; the library definition is exactly `circulantGraph {1}` for a positive modulus. The underlying `fromRel` construction symmetrizes adjacency and removes loops. The library's `circulantGraph_eq_symm` and cycle adjacency lemmas confirm that these are precisely steps +1 and -1, including the wraparound edge. The submitted `graph_is_cayley` equality is definitional. This matches the word metric with generators and inverses.

3. **Potential controls every edge, including wraparound.** The potential is the concrete function `min a (1021-a)` on canonical representatives. `edge_potential` starts from the actual graph adjacency lemma and converts modular differences to the two remainder equations. The arithmetic lemma treats arbitrary representatives in the full valid range, so there is no omitted edge or special-case assumption. In particular, the edge 1020--0 has potentials 1 and 0.

4. **Every walk, then the actual shortest-path distance.** `potential_le_walk` inducts on arbitrary `graph.Walk u v`; it does not inspect a selected path. At vertices 0 and 510, the exact potentials are 0 and 510, forcing every connecting walk to have length at least 510. `graph_connected` is a genuine library connectivity proof. The inspected metric API provides a walk whose length equals `graph.dist`, so the proof transfers to the actual shortest-path distance. Connectivity also excludes Mathlib's disconnected-pair junk value of zero.

5. **Actual finite diameter.** The submitted diameter is the double `Finset.univ.sup` of the actual graph distance over all vertices. For this finite connected nonempty graph this is exactly the usual maximum pairwise distance. The two `Finset.le_sup` steps establish the witness distance is below that maximum, yielding diameter at least 510. No separate numerical diameter or unchecked formula is substituted.

6. **Natural and binary logarithms.** The natural-log proof uses positivity, monotonicity, `1021 < 2^10`, the logarithm-of-a-power identity, and `log 2 < 1`. It obtains `0 <= log 1021 < 10`; hence three times its square is below 300, which is below 510. The binary theorem separately proves `log 2 > 0`, divides the same strict inequality by this positive denominator, and supplies nonnegativity before squaring. Thus neither proof squares an inequality with an uncontrolled sign or reverses a denominator inequality incorrectly. The statements in the paper are consistent with these exact formal comparisons.

7. **Correct quantifier and contradiction.** `ClaimedDiameterBound` quantifies over finite simple groups in additive notation and generating sets, with connectivity supplied. Substitution of the actual group and singleton generator produces precisely the inequality contradicted by the strict diameter bound. Restricting to connected generated Cayley graphs is appropriate for the stated word metric. A universal claim over finite simple groups necessarily includes this finite prime cyclic example.

8. **Claim boundary.** The proof disproves the literal universal upper bound. It makes no claim about nonabelian finite simple groups, the PSL(2,p) family clause, an exact value of the diameter, or arbitrary logarithm bases. The proven lower bound alone suffices. This boundary is explicit in both `main.tex` and `README.md`.

## Evidence boundary

This review is based on the complete submitted source, its mathematical correspondence, the named Mathlib implementations, and the existing actual direct-Lean axiom output. The reviewer did not claim a separate compiler run or PDF visual inspection. The parent agent is responsible for the recorded fresh build, final PDF inspection, source freshness, duplicate check, and publication. Subsequent changes to the Lean file require renewed review against its hash.
