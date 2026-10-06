# Disproof of conjecture `00000002712`

The conjecture asserts nonnegativity of the g-vectors of flag simplicial
complexes. It does not restrict the class to homology spheres or simplicial
polytopes. The counterexample is the clique complex of the one-edge graph
`K₂`, the full 1-simplex. It is connected, pure, and flag.

Its faces are the empty face, both singleton vertices, and the full edge.
Lean defines those faces as graph cliques and obtains their counts by filtering
the actual finite face set, rather than taking the f-vector as an assumption.
The resulting data are `f_{-1}=1`, `f₀=2`, and `f₁=1`. The standard f-to-h
transform at rank `d=2` gives `h=(1,0,0)`. The standard truncated g-vector
includes indices through `floor(d/2)=1`, so `g₁=h₁-h₀=-1`. This single valid
index contradicts the claimed nonnegativity.

`lean/Counterexample.lean` formalizes the graph, its clique complex, face
closure, flag property, connectedness, purity, dimension/rank, face counts,
the standard polynomial transform, and the negative g-entry. The formal proof
uses no `sorry`, `native_decide`, or extra axioms.

The g-vector has its exact formal truncated index type
`Fin (complexRank / 2 + 1)`. The final `actual_counterexample` theorem
combines connectedness, flagness, purity, dimension one, and a negative
entry. There is no sphere hypothesis in the original conjecture; this
submission does not refute a modified sphere-only assertion.

## Reproduction

Inside `lean/`, run `lake update`, `lake exe cache get`, and `lake build`.
Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` are pinned, with a lockfile.
The build succeeds without warnings; the printed theorem audits have only
the foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.
The report is `solution.tex` with its visually checked PDF `solution.pdf`.
