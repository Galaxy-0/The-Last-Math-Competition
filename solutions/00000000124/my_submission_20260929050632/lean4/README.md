# Lean 4 certificates for the disproof of TLMC conjecture 00000000124

Self-contained core-Lean project (no dependencies). Toolchain:
`leanprover/lean4:v4.33.1`.

## Build and audit

```
lake build
lake env lean Check.lean
```

`Check.lean` runs `#print axioms` on all 138 theorems; every line reads
`does not depend on any axioms` (zero `sorry`, zero `propext`, zero
`Quot.sound`, zero `Classical.choice`).

## What is proved

For each of the 22 odd primes `q < 200` with `ord_q(2) = q-1`
(`q = 3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83, 101, 107, 131, 139, 149,
163, 173, 179, 181, 197`):

- `pr_q` — 2 is a primitive root mod `q`: `2^(q-1) % q = 1` and
  `2^((q-1)/f) % q ≠ 1` for each prime `f | q-1` (all `decide`);
- `dlog_ok_q` / `dl_len_q` / `cover_q` — explicit discrete-log witness lists
  `dlogs_q` (entry `j` is `n` with `2^n % q = j+1`), checked by the Boolean
  predicate `dlogOk` and converted to the semantic statement
  `∀ k, 1 ≤ k → k < q → InOrbit q k` by the hand-proven lemma
  `dlogOk_implies`;
- `lm_q` — `IsLeastMissing q q`: every positive `k < q` occurs in the orbit and
  `q` does not (via `not_inOrbit_self`, from `Nat.mod_lt`), i.e. the least
  positive integer missing from `{2^n mod q}` is exactly `q`, so `m(q) = q`;
- `pw_q` — with `ell = floor(log2 q)`: `2^ell ≤ q < 2^(ell+1)` and
  `ell * ell < q`, the concrete gap `m(q) = q > (log_2 q)^2`.

Flagships: `attack_101` (the verification verdict's spot check: primitive-root
certificate + `m(101) = 101` + `6*6 = 36 < 101`) and `attack_3`
(`m(3) = 3`, `1 < 3`).

Supporting definitions: `InOrbit q k := ∃ n < q-1, 2^n % q = k`;
`IsLeastMissing m q := (∀ k, 1 ≤ k → k < m → InOrbit q k) ∧ ¬InOrbit q q`.
The witness lists were produced by an independent recomputation
(`../reproduce.py`); any wrong number would make the corresponding `decide`
fail, so the lists are self-checking.

Build options: `set_option maxHeartbeats 1000000` and
`set_option maxRecDepth 10000` (needed by the deeper `decide` evaluations),
both on standalone lines.
