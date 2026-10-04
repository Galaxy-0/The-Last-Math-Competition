# Adversarial self-review: conjecture 00000003476

Verdict: PASS after a separate mathematical and source-correspondence pass.
This problem was developed and reviewed by a single AI agent. No
independent or external review is claimed.

1. Reading. Both source languages state an equivalence for subdividing
   an edge: the Wiener index decreases if and only if the betweenness of
   the edge is below a quarter of the vertex count. No class of graphs
   is excluded; the Wiener index needs connectedness, which is assumed.
2. All four objects exist in Lean, for arbitrary finite graphs. The
   graph and its distance are Mathlib's. subdivide removes the edge ab
   and adds one vertex adjacent to exactly a and b; symmetry and
   irreflexivity are proved. wiener is half the ordered distance sum.
   sigma counts walks whose length equals the distance; such walks are
   exactly the shortest paths. sigmaThrough adds the condition that the
   edge belongs to the walk's edge list. This addresses the reason the
   earlier submission was rejected.
3. Betweenness of an edge of K9. sigma_top and sigmaThrough_top are
   proved for the complete graph on any vertex type by showing that a
   walk of length one is a single edge. The count of contributing
   ordered pairs is kernel-checked to be 2, so the unordered value is 1.
   Conventions: unordered 1, ordered 2, endpoints omitted 0; all are
   below 9/4 and below 10/4. Both the unordered and the ordered version
   of the criterion are refuted formally. K9 rather than K5 is used
   because 2 < 9/4 but 2 > 5/4.
4. Wiener index of K9. The ordered sum is kernel-checked to be 72, i.e.
   W = 36.
5. Wiener index after subdivision. The subdivided graph is proved
   connected through the hub vertex 2, which is adjacent to every old
   vertex and reaches the new vertex through vertex 0. For a connected
   graph every distance between distinct vertices is at least one, so
   the ordered sum on 10 vertices is at least 90, i.e. W >= 45 > 36.
   Lean proves this bound, not the exact value. The exact value 53 was
   computed by hand: the pairs at distance two are {a,b} and {w,x} for
   the seven other vertices x. The paper says which of the two is
   formalised.
6. The final statement. ClaimedCriterion quantifies over every finite
   type, every connected graph and every edge, and states the
   equivalence in Q. conjecture_false uses the direction from small
   betweenness to decrease, at K9 and the edge 01, and contradicts
   wiener_increases.
7. General proposition (not formalised). The walk-projection argument
   was rechecked: the new vertex has only the neighbours a and b, so a
   walk between old vertices passes it only as a,w,b; b,w,a; a,w,a or
   b,w,b, and each passage can be shortened or removed in G.
8. Bipartite remark (not formalised). In K7,7 an edge uv has betweenness
   1 + 2(6/7) = 19/7: the pair {u,v} contributes 1; each of the 6 pairs
   {u,u'} and of the 6 pairs {v,v'} has 7 shortest paths, one through
   uv. 19/7 < 14/4.
9. Earlier submission. The account is limited to the pull request's
   description and the reviewer's comment, both read from the public
   repository, plus the observation about the ordered convention, which
   is a calculation.
10. No sorry, admit, native_decide, opaque or custom axiom. The printed
    axioms are propext, Classical.choice and Quot.sound only. The fresh
    build and direct Lean run are recorded in BUILD.json. All PDF pages
    were opened and inspected after the final compilation.
