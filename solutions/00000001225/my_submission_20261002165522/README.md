# Disproof of conjecture `00000001225`

**Verdict: FALSE under both natural readings of "survival count".**

## The conjecture (verbatim from `conjectures/00000001225.md`)

> Definition: The firefighter problem (protecting one vertex per step).
> Conjecture: The trees whose firefighter survival count is at least n/2 are
> exactly the caterpillar class (a half-survival structure).

**Object consistency.** We attack exactly: "survival count" (firefighter,
one protected vertex per turn, protect-then-spread) and "the caterpillar
class" (tree whose leaf-stripped remainder is a path). The conjecture does
not specify the ignition convention, so both standard readings are refuted.

## Reading A — adversarial ignition (the standard convention): star fails

K_{1,6} (center 0, leaves 1..6) **is a caterpillar** (stripping leaves leaves
one vertex). Ignite the center; whatever leaf `p` the firefighter protects
first, the fire takes the other five leaves **in one spread** and then stops
(diameter 2 — every neighbor of a burned vertex is burned or protected).
Survival = 1, and 2·1 = 2 < 7: **survival ≥ n/2 fails for a caterpillar**.
All six protections checked (Lean: `star_p1`…`star_p6`, `star_stable1`…`6`).

## Reading B — existential ignition: spider qualifies

The 3-legged spider S(2,2,2) (legs 0-1-2, 0-3-4, 0-5-6) is **not a
caterpillar**: stripping leaves {2,4,6} leaves K_{1,3} whose center has
degree 3 > 2, not a path. Yet igniting leaf 2 and protecting vertex 1
contains the fire immediately (2's only neighbor is 1): survival = 6, and
2·6 = 12 ≥ 7: **a non-caterpillar achieves survival ≥ n/2**.
(Lean: `spider_contained`, `spider_achieves_half`.)

Either clause of "exactly the caterpillar class" fails, so the biconditional
is false on both readings.

## Reproduce

`python3 reproduce.py` — full optimal-play search (memoized game tree) over
both trees and all 7 sources reproduces: star survival by source
`{0:1, leaf:6,…}`; spider `{center:3, mid-leg:5, leaf:6}`; i.e. star
worst-case 1 < 3.5 and spider best-case 6 ≥ 3.5. Exit 0 iff checks pass.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 18 theorems,
all `does not depend on any axioms`.
