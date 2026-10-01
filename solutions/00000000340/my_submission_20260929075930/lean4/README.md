# Lean 4 certificate — disproof of TLMC conjecture 00000000340

Self-contained core Lean 4 (no Mathlib, no external dependencies). All theorems
are proved with `rfl`/`decide` and explicit `Nat` arguments — **zero axioms,
zero `sorry`**.

Contents of `Main.lean` (namespace `TLMC340`):

- `a` / `prodA` — partial quotients of `√2 = [1; 2, 2, …]` and their prefix products;
- `prodA_eq` — the identity `∏_{j<N} a j = 2^(N−1)`, i.e. `G_N(√2) = 2^((N−1)/N) → 2`;
- `prodA_1000` — `∏_{j<1000} a j = 2^999` exactly;
- `G1000_bounds` — `199^1000 ≤ 2^999·100^1000 ≤ 201^1000`, i.e. `1.99 ≤ G_1000 ≤ 2.01` (decide);
- `prodA_le_pow2` — `G_N ≤ 2` for every `N` (refutes `limsup = ∞`);
- `pow2_le_sq_prodA` — `G_N² ≥ 2` for every `N ≥ 2`, so `G_N ≥ √2 > 1` (refutes `liminf = 1`);
- `G_ge_199` — `G_N ≥ 1.99` for every `N ≥ 139` (sharp threshold);
- `disproof` — conjunction of all of the above.

## Build and verify

Requires elan/Lean toolchain `leanprover/lean4:v4.33.1` (see `lean-toolchain`).

    lake build
    lake env lean Check.lean

`Check.lean` prints `#print axioms` for every main theorem; each must report
"does not depend on any axioms".
