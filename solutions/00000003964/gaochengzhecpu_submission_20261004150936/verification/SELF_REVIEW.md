# Adversarial self-review: conjecture 00000003964

Verdict: PASS after a separate mathematical and source-correspondence pass.
This is the authoring parent's review. A distinct delegated review is
recorded separately; neither is external peer review.

1. Both source languages quantify over every finite simple group. There
   is no nonabelian hypothesis. Prime cyclic groups satisfy the standard
   definition and Mathlib's actual IsSimpleAddGroup typeclass. The paper
   explicitly identifies this scope and does not claim the nonabelian case.
2. The actual group is ZMod 1021, with cardinality 1021. Primality is proved
   by the kernel-checked norm_num prime extension, not asserted as an axiom.
3. The actual additive-subgroup closure of {1} is proved to be top. Graph
   connectivity is independently supplied by the actual cycle-graph API.
4. graph_is_cayley is definitional equality with Mathlib circulantGraph.
   This graph uses generators and inverses, exactly the undirected word
   metric described in the paper; no alternate shortcut edges are added.
5. The potential uses actual vertex representatives. A natural-number
   lemma proves its edge inequality from modular differences. Every edge
   is shown to satisfy that premise. Induction handles every actual Walk.
6. A shortest actual Walk exists by connectivity and has length graph.dist.
   Evaluating the endpoint potential proves 510 <= graph.dist 0 510.
   There is no assumption or replacement definition assigning this distance.
7. diameter is the finite maximum of actual graph distances. Each distance
   is proved <= this maximum. The custom wrapper only expresses the usual
   finite-graph diameter; it does not encode the claimed lower bound.
8. Lean checks both natural-log and binary-log strict bounds. The estimates
   are intentionally loose (less than 300 versus at least 510), so no
   floating-point approximation or rounding assumption is involved.
9. ClaimedDiameterBound quantifies over actual finite simple additive groups
   and arbitrary generating sets, with connectivity. Additive notation
   changes no group axiom and does not impose commutativity. A connected
   counterexample refutes even this necessary universal clause.
10. The final theorem negates that clause. No result about the additional
    PSL(2,p) extremal claim is required to refute the stated conjunction.
11. Fresh build, direct Lean, axiom audit and PDF checks are separate actual
    evidence in BUILD.json. Only the three standard foundational axioms
    are permitted; final visual review is marked only after all pages
    have been opened and inspected.
