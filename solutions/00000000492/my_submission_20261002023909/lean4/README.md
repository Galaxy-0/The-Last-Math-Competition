# Lean 4 verification for the disproof of TLMC conjecture 00000000492

Core Lean 4 only (toolchain `leanprover/lean4:v4.33.1`, **no Mathlib**).

`Main.lean` concretizes the attack numbers of the disproof as `Nat` theorems:

- `cap3` — any 3-cell tableau has hook sum at most `9 = n²` (cap: `(Σ hooks)/n² ≤ 1`);
- `overshoot` — for every `n ≥ 3`, `3 < n² − 1`, i.e. the conjectured `(n²−1)/3` exceeds the cap;
- `row3_sum`, `row3_disproof` — counterexample `n = 3`, row shape `(3)`: hooks `3+2+1 = 6`,
  `6/9 = 2/3 ≠ 8/3` (cross-multiplied `6·3 ≠ 8·9`);
- `cap_gap_n3` — even the maximal sum `9` gives ratio `1 < 8/3`;
- `square3_sum`, `square3_disproof` — square reading: `3×3` hook sum `27`, `27/9 = 3 ≠ 8/3`;
- `row3_divn_disproof`, `cap_gap_divn_n4`, `overshoot_divn` — divide-by-`n` reading collapses
  (`6/3 = 2 ≠ 8/3`; `16/4 = 4 < 5`; `3n < n² − 1` for `n ≥ 4`);
- `shape21_expectation`, `shape21_disproof` — randomization over tableaux cannot help:
  shape `(2,1)` gives `E[Σ hooks] = 5`, `5/9 ≠ 8/3`.

`Check.lean` audits every theorem with `#print axioms`; the expected output is that
each one `does not depend on any axioms` (zero axioms, zero `sorry`).

## Build and verify

```sh
lake build
lake env lean Check.lean
```

Expected: `lake build` succeeds with no warnings/errors, and `Check.lean` prints
`'...' does not depend on any axioms` for all 12 theorems.

If `elan` is not on the default `PATH`, set `ELAN_HOME` to the elan installation
directory and prepend `$ELAN_HOME/bin` to `PATH` first.
