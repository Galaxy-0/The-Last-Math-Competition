# Lean 4 formalization: disproof of TLMC 00000000450

Core Lean 4 (v4.33.1), **no Mathlib, zero axioms, zero `sorry`**.

`Main.lean` defines:

- `seqs n` — the area sequences of Dyck paths of semilength `n`
  (sanity-checked: `2, 5, 14, 42` for `n = 2..5`, the Catalan numbers);
- `areaStat` / `dinvStat` — the classical area and (primary + secondary)
  dinv statistics, so `C_n(q,t) = Σ q^{areaStat} t^{dinvStat}`;
- exact evaluations of `C_n(ζ, ζ^{-1}) = Σ ζ^{area − dinv}` in the
  cyclotomic integer rings `Z[ζ]/(Φ_n)` for `n = 2..6`:
  `C2 = −2`, `C3 = 2 ≠ 4`, `C4 = −2`, `C5 = 2 ≠ 36`, `C6 = −2`;
  boundary `n = 1`: value 1 = (1+1)^0 (conjecture holds there);
- the `n = 2` polynomial identity `C_2(q,t) = q + t` (terms `(area,dinv) =
  (0,1),(1,0)`), giving `C_2(−1,−1) = −2 ≠ 3^{1/2}` (whose square is
  `3 ≠ 4`, and √3 is irrational — see the write-up).

All proofs are pure kernel computation (`rfl`/`decide`).

## Build and audit

```
export ELAN_HOME=/Users/mychanging/.workbuddy-ai/binaries/lean/elan
export PATH="$ELAN_HOME/bin:$PATH"
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem; each must (and does)
report **"does not depend on any axioms"**.
