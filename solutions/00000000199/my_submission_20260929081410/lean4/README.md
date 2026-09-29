# Lean 4 verification — Disproof of conjecture 00000000199

Core Lean 4 only (no Mathlib). `Main.lean` concretizes the attack against the
conjecture that `S = Σ_{n≥0} 1/(n²+n+2)` is an explicit Q-linear combination of
digamma values at **cube roots of unity**:

- `r199_is_root`: `r = (-1+i√7)/2` (element `(-1+s)/2` of `Q(√-7)`, `s² = -7`)
  satisfies `r² + r + 2 = 0` — it is a genuine root of the denominator `n²+n+2`.
- `r199_modsq_eq_two` / `r199_modsq_ne_one`: `|r|² = r·conj(r) = 2 ≠ 1` —
  not unimodular, hence not a root of unity.
- `r199_cubed_ne_one`, `rbar199_cubed_ne_one`, `r199_sq_ne_one`, `r199_ne_one`:
  `r³ ≠ 1`, `conj(r)³ ≠ 1`, `r² ≠ 1`, `r ≠ 1` — not a 1st/2nd/3rd root of unity.
- `disc_199`, `disc_unity`, `disc_199_ne_disc_unity`: discriminants
  `z²+z+2 ↦ -7` vs `z²+z+1 ↦ -3` differ; cube roots of unity belong to the
  discriminant `-3` world.
- `omega3_*`: the contrast in `Q(√-3)`: `ω = (-1+i√3)/2` satisfies
  `ω²+ω+1 = 0`, `ω³ = 1`, `ω·conj(ω) = 1`.
- `psum40_val`, `psum60_val`: exact fixed-point rational partial sums
  `Σ_{n<N} 1/(n²+n+2)` for `N = 40, 60` (40/60-term exact computations over
  integers: `psum40/P40 = 1.161837745283165...`, `psum60/P60 = 1.170163756273512...`).
- `ab_sum`, `ab_prod`, `shift_n0..shift_n3`: the partial-fraction mechanism
  sampled concretely (`a+b = 1`, `ab = 2`, `(n+b)-(n+a) = b-a`).

All proofs are closed computations (`rfl`/`decide` on integer literals).
**Zero axioms, zero `sorry`** — verified by the audit below.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem; each line must read
`... does not depend on any axioms`.

Toolchain: `leanprover/lean4:v4.33.1` (see `lean-toolchain`).
