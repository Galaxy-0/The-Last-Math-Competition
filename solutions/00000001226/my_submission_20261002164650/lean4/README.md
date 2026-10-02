# Lean formalization — disproof of TLMC conjecture 00000001226

Core Lean only (no Mathlib, no external dependencies), bare `Nat`/`List`
computation.  All proofs are `decide`/explicit terms; the axiom audit
(`lake env lean Check.lean`) reports that every theorem depends on **no
axioms** (in particular no `sorry`, no `propext`, no `Quot.sound`, no
`Classical.choice`, no `Lean.ofReduceBool`).

## What is formalized

The firefighter process on `K4` (vertices `0,1,2,3`, complete graph, fire
starts at `0`) is forced — every strategy yields the same outcome:

1. `savedF1_1/_2/_3`, `every_strategy_f1` — with `f = 1` (standard), every
   first move `c ∈ {1,2,3}` saves exactly one vertex; no second move exists.
2. `expectation_uniform_f1` — uniform random firefighting:
   `(1 + 1 + 1) / 3 = 1`.
3. `expectation_any_f1` — distribution-free: for any weights `w1 w2 w3`,
   `w1 * savedF1 1 + w2 * savedF1 2 + w3 * savedF1 3 = w1 + w2 + w3`
   (the expected survival is `1` under every probability law).
4. `savedF2_12/_13/_23`, `savedF3_val` — forced outcomes `2` and `3` for
   `f = 2, 3`.
5. `no_solution` — `∀ s : Nat, 5 * s ≠ 13` (13 is not a multiple of 5):
   the claim `E[saved] = 0.65 · 4 = 13/5` would force `5 * E = 13`.
6. `claim_false_f1/f2/f3`, `conjecture_1226_false` — the assembled
   disproof.

Hence the expected firefighter survival on 3-regular graphs is not `0.65n`;
it fails on the first member of the class, for every number of firefighters
and every (random or optimal) strategy.

## Build and audit

```
lake build
lake env lean Check.lean
```

Expected: every `#print axioms` line ends with
*does not depend on any axioms*.

(If elan lives in a nonstandard place:
`export ELAN_HOME=<elan dir> && export PATH="$ELAN_HOME/bin:$PATH"` first.)
