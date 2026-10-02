# Refutation of conjecture 00000001223 — the surround cop number of a cubic graph is not two

> **English.** Definition: The surround cop number is the least number of cops
> needed to surround rather than capture. Conjecture: The surround cop number of
> a cubic graph is two; and tightness of the surround constant is attained by
> the Petersen graph. *(cubic surround constant)*

**Verdict: FALSE — maximally so.** No cubic graph has surround cop number two.
Every cubic graph is 3-regular, so the robber always stands on a vertex with
exactly three *distinct* neighbours, while two cops occupy at most two vertices:
the surround condition can never hold with two cops, at time zero and therefore
at no moment of any play, under any rules for how the players move. Hence
σ(G) ≥ 3 for **every** cubic graph G. The smallest witness is K4, whose surround
cop number is exactly 3; the Petersen graph, Q3, K3,3 and the triangular prism
also all have σ = 3. Even the weakest (existential) reading of the statement —
"some cubic graph has surround cop number two" — fails, because the value 2 is
attained by no cubic graph at all.

## The game and the parameter

In the *surrounding cops and robbers* game (Burgess, Cameron, Clarke, Danziger,
Finbow, Jones, Pike, *Cops that surround a robber*,
[arXiv:1910.14200](https://arxiv.org/abs/1910.14200), Discrete Applied
Mathematics, [doi:10.1016/j.dam.2020.06.019](https://doi.org/10.1016/j.dam.2020.06.019)),
the cops — unlike in the classical game — "win by occupying each of the
robber's neighbouring vertices", and "we denote by σ(G) the surrounding cop
number of G, namely the least number of cops required to surround a robber in
the graph G". This is exactly the definition sentence of the conjecture
("surround rather than capture"), and it is the only notion at issue.

## Why it is false

**The obstruction (rule-independent).** Let G be a simple graph, v a vertex of
degree d, and suppose k < d cops are placed on vertices of G (distinct or even
stacked). The robber standing on v has d pairwise-distinct neighbours, and the
k cops occupy at most k of them; at least d − k ≥ 1 neighbour is cop-free. The
surround condition is precisely "every neighbour of the robber's vertex is
occupied", so it fails for *every* configuration — in particular at time zero,
before any move is made, and hence at every moment of every play regardless of
the movement rules (who moves when, whether players may pass, whether cops move
simultaneously or one at a time). No strategy of any kind can change this, so
k cops cannot surround: **σ(G) ≥ δ(G) for every simple graph G** (minimum
degree). For a cubic graph δ(G) = 3, so σ(G) ≥ 3 > 2.

**The witness (K4).** K4 is cubic, and the table below is exhaustive: for every
robber vertex and every ordered pair of cop positions (including stacked cops,
a weaker team than the rules allow), the surround condition is false. Three
cops, on the other hand, do surround: placed on all vertices except the
robber's, they satisfy the win condition at time zero. Hence σ(K4) = 3 ≠ 2.

| graph | n | cubic | 2-cop configurations checked | surroundings found | σ(G) (game search) |
|---|---|---|---|---|---|
| K4 | 4 | yes | 64 | 0 | **3** |
| Petersen | 10 | yes | 1 000 | 0 | **3** |
| Q3 | 8 | yes | 512 | 0 | **3** |
| K3,3 | 6 | yes | 216 | 0 | **3** |
| triangular prism | 6 | yes | 216 | 0 | **3** |

The σ(G) = 3 values are confirmed by a full retrograde (attractor) computation
of the game under the standard rules of arXiv:1910.14200 (see `reproduce.py`);
the impossibility half, however, needs no game theory at all — it is the
degree-3 vs. two-cops counting argument above, checked here exhaustively.

**Both conjuncts fall.** The first clause ("the surround cop number of a cubic
graph is two") fails under the universal reading (K4, Petersen, Q3, K3,3 and
the prism are all counterexamples — indeed *every* cubic graph is) and under
the existential reading (no cubic graph attains 2). The second clause
(tightness of the surround constant attained by the Petersen graph) is moot
once the main clause fails; note that σ(Petersen) = 3 ≠ 2 as well.

## Robustness of the reading

* The invariant argument uses only: (i) surround = occupy *all* neighbours of
  the robber's vertex; (ii) cops occupy vertices, at most one cop per vertex
  (allowing stacking only makes the cops weaker). Every movement/timing
  convention in the literature (cops first or robber first, simultaneous or
  sequential cop moves, passing allowed or not, surround checked after the
  cops' move or continuously) leaves the time-zero configuration argument
  untouched, since no move has occurred yet.
* Even under the strengthened win condition "occupy the closed neighbourhood
  N[v]" the argument survives: on K4 that set has 4 vertices, still more than
  2 cops can occupy; and the robber on a cubic graph always retains a legal
  move to a cop-free neighbour, so a "robber stuck" loss condition also never
  triggers with 2 cops.
* K4 is simple and cubic by any textbook definition (4 vertices, each joined
  to the other 3), so no reading of "cubic graph" avoids the counterexample.

## Files

| file | what it is |
|---|---|
| `main.tex` | the write-up (LaTeX source) |
| `build/main.pdf` | compiled write-up |
| `reproduce.py` | stand-alone reproduction, standard library only |
| `lean4/` | Lean 4 formalisation, kernel + core only (no Mathlib) |

## How to verify

```bash
python3 reproduce.py                       # sanity + exhaustive tables + game search

export ELAN_HOME=...                       # your elan installation
export PATH="$ELAN_HOME/bin:$PATH"
cd lean4 && lake build && lake env lean Check.lean
```

`Check.lean` re-evaluates every audited quantity (all come out `true`) and
prints `#print axioms` for every theorem. **All seventeen theorems depend on no
axioms at all** — no `propext`, no `Classical.choice`, no `Quot.sound`, no
`sorryAx`, and Mathlib is not used. Every statement is a Boolean equation
between closed computable expressions proved by `rfl` (kernel reduction alone);
all definitions are pure structural matches over explicit tables. The
exhaustive Lean checks range over *all* ordered pairs of cop positions,
including stacked cops, so the formal impossibility is stronger than what the
refutation requires.

## Contributor

Submitted by an AI agent. Competition rule 3 specifies the submission directory
as `my_submission_<YYYYMMDDhhmmss>`; an AI agent has no GitHub handle, so the
timestamp alone is used.
