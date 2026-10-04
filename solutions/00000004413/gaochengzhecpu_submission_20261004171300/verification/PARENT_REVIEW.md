# Parent review of conjecture 00000004413

Verdict: PASS for a disproof of the stated upper bound, with the limits listed in point 5.

Reviewer: the coordinating AI agent that delegated this problem. This is an internal review
within the same workflow, not an external or independent peer review. No source file was
changed in review.

1. Source and reading. Both languages assert an upper bound (d-1)^l / (2l) for the measure of
   cycles of length l in a graph limit of degree bound d, and that the bound is attained and
   optimal for the d-regular tree. A finite graph with a uniformly random root is a
   bounded-degree graph limit, and its cycle measure is the number of l-cycles per vertex.
2. Objects. Graphs, degrees and cycle graphs are Mathlib's. A cycle of length L in G is an
   injective graph homomorphism from `cycleGraph L`; the measure divides their number by 2L
   and by the number of vertices. This counts genuine cycles.
3. Argument. The cycle graph C_l (l >= 3) is 2-regular. Its l rotations and l reflections are
   2l distinct injective endomorphisms, so the measure is at least 1/l, above the claimed
   1/(2l) for d = 2. I rechecked the distinctness argument (i + k = k' - i for all i forces
   2 = 0 in Z/l). Lean proves the inequality for every l >= 3.
4. Final statement. `ClaimedUpperBound` quantifies over all finite graphs, all d and all
   L >= 3 with maximum degree at most d; `conjecture_false` negates it.
   `conjecture_false_every_length` gives a counterexample for each length.
5. Limits, all stated in the paper. The formal refutation is at d = 2 only. For d >= 3 the
   upper bound is true (paper Proposition 2 gives the sharper d(d-1)^(l-2)/(2l)), and the
   conjecture fails there only through the attainment clause: a tree has no cycles. Those
   statements are proved on paper and are not formalised. Other normalisations of the measure
   are larger, so the violation persists. I checked Proposition 2 by hand.
6. Earlier submission. PR #302 was withdrawn by its author without a reviewer verdict. I
   fetched its Lean file and confirmed the description in the paper: its closed walks were not
   required to be injective, its K3 instance was sound, and its tree statement was the
   positivity of the bound. The paper says its example and conclusion were correct.
7. Evidence. `validate_draft.py`: fresh build with warnings as errors, only `propext`,
   `Classical.choice`, `Quot.sound`, three PDF pages, no TeX warnings; recorded hashes match
   the files. All three rendered pages (prefix 4d9f7b964488) were opened and inspected: no
   clipping, overflow or missing glyphs.
