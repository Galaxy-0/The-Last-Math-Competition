# Solution Review — Conjecture 00000003730 (PR 715)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005135139`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Official conjecture read (EN+CN): energy = sum of absolute eigenvalues; maximum of the sum attained by complete bipartite graphs; minimal tree is the path. `conjecture.md` byte-identical to the official file.
- LaTeX: independent rebuild exits 0; content matches; extraction artifacts only.
- Lean build: exit 0, 8708 jobs, zero errors/warnings.
- Forbidden content: none.
- Axioms: my independent `CheckJ6.lean` over all 13 theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- Auxiliary code: verification logs verified (CRLF manifest artifact only).
- Sanity check: numpy eigenvalues — E(K₃) = 4, E(K_{1,2}) = 2√2, E(K_{2,2}) = 4, E(P₄) = 2√5 ≈ 4.472, E(K_{1,3}) = 2√3 ≈ 3.464; all match the Lean-computed values.

## Semantic audit
Unlike the rejected PR #226 it supersedes, this submission defines energy genuinely: `energy G = ∑ i, |(G.isHermitian_adjMatrix ℝ).eigenvalues i|`, i.e. the sum of the eigenvalues (with multiplicity) of the real symmetric adjacency matrix given by Mathlib's spectral theorem — the standard definition of graph energy. No numeral games; the decisive theorems quantify over graphs.

Clause (i): `MaxIsCompleteBipartite` (∀ n ∃ a b, a+b = n ∧ every graph on n vertices has energy ≤ E(K_{a,b})) is refuted via K₃: `energy_top` proves E(K_n) = 2(n−1) for all n ≥ 1 (every eigenvalue is n−1 or −1, derived from the eigenvector equation (λ+1)v_u = Σw v_w — not hardcoded), and `energy_cb` proves E(K_{a,b}) = 2√(ab) (eigenvalues 0, ±√(ab) via the two-part sums S, T), whence `energy_cb_le` (2√(ab) ≤ a+b, AM–GM) and `completeGraph_beats_completeBipartite` give E(K_{a,b}) < E(K_n) for every a+b = n ≥ 3. Since the conjecture's ∃a b is refuted for every choice simultaneously, the reading is robust. The weaker "bipartite graphs only" reading is also refuted: at n = 4, P₄ is bipartite (Mathlib's bicoloring) with E = 2√5 > 4 ≥ E(K_{a,b}) — a nice point, since energy is not edge-monotone and P₄ ⊂ K_{2,2} has the larger energy.

Clause (ii): `MinTreeIsPath` (∀ n, every tree T on n vertices has E(P_n) ≤ E(T)) is refuted at n = 4: `star4_isTree` and `pathGraph4_isTree` prove both graphs are trees (connected + n−1 edges), `energy_star4` = 2√3 and `energy_P4` = 2√5 (via the eigenvalue relations λ² ∈ {0,3} for the star and λ⁴−3λ²+1 = 0 for the path, each derived from the eigenvector equations by linear combinations), so E(star) < E(path) — the path is not the minimizer (indeed, as the literature says, the path is the maximizer among trees). All quantifiers match the official text's 极小的树为路径.

## Issues found
- None blocking.

## Verdict
APPROVED. Both clauses of the conjecture are false and both are refuted in Lean from the actual spectral definitions, with all four energies (K_n, K_{a,b}, P₄, K_{1,3}) proven for general parameters and numerically confirmed; the earlier submission's defects (no graphs, no eigenvalues) are fully remedied.
