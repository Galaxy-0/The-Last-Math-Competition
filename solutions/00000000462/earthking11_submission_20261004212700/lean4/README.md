# Lean 4 formalisation — disproof of conjecture `00000000462`

Core Lean only (`import Std`; **no Mathlib**, no `sorry`, no `native_decide`).

```sh
lake build
lake env lean Check.lean
```

## What is being refuted

The conjecture claims that `τ(C_n(1,2))`, the number of spanning trees of the
square of the `n`-cycle, "satisfies a linear recurrence whose largest real
characteristic root tends to `α²`, where `α = 2+√3`".

The formalisation establishes the negation by proving:

1. the exact closed form `τ(n) = n·(L(2n) + 2(−1)^(n+1))/5`, where `L` is the
   Lucas sequence (this is the sequence the conjecture is about);
2. `τ` satisfies the six-term linear recurrence
   `τ(n+6) = 4τ(n+5) − 10τ(n+3) + 4τ(n+1) − τ(n)`, whose characteristic
   polynomial is `p(x) = x⁶ − 4x⁵ + 10x³ − 4x + 1 = ((x+1)(x²−3x+1))²`;
3. `p` does not vanish at `α² = (2+√3)² = 7+4√3`: `p(α²) = 2615536 + 1510080√3`
   in `Z[√3] ≅ Z[t]/(t²−3)`, which is nonzero.

Since a characteristic root of a linear recurrence must be a root of every
annihilating polynomial, and `α²` is not a root of `p`, `α²` cannot be a
characteristic root of any recurrence satisfied by `τ`.

## Statement table

| Lean name | Statement |
|:--|:--|
| `L`, `L_rec` | Lucas numbers and their defining recurrence |
| `M`, `M_rec` | `M n = L(2n)`; `M(n+2) = 3M(n+1) − M(n)` (characteristic polynomial `x²−3x+1`) |
| `s`, `s_succ`, `s_add_two` | the sign sequence `s n = (−1)^(n+1)`, with definitional shift rule |
| `u`, `u_rec` | `u n = L(2n) + 2(−1)^(n+1)`; `u(n+3) = 2u(n+2) + 2u(n+1) − u(n)` (characteristic polynomial `x³−2x²−2x+1`) |
| `u3`, `u4`, `u5`, `u6` | iterated forms: `u(n+3) = 2C+2B−A`, `u(n+4) = 6C+3B−2A`, `u(n+5) = 15C+10B−6A`, `u(n+6) = 40C+24B−15A`, where `A = u n`, `B = u(n+1)`, `C = u(n+2)` |
| `P_zero` | `u(n+6) − 4u(n+5) + 10u(n+3) − 4u(n+1) + u n = 0` (the operator `p(E)²` applied to `u`) |
| `Q_zero` | `6u(n+6) − 20u(n+5) + 30u(n+3) − 4u(n+1) = 0` (the correction forced by the factor `n`) |
| `c`, `c_rec` | `c n = n·u(n) = 5·τ(n)`; `c(n+6) = 4c(n+5) − 10c(n+3) + 4c(n+1) − c(n)` |
| `five_dvd_u` | `5 ∣ u n` for all `n` (three-step induction from `u 0 = 0`, `u 1 = u 2 = 5`) |
| `five_dvd_c`, `five_mul_tau` | `5 ∣ c n` and `5·τ(n) = c n` |
| `tau`, `tau_rec` | `τ(n) = c n / 5`; **`τ` satisfies the six-term recurrence** |
| `tau_5` … `tau_12` | the known spanning-tree counts `125, 384, 1183, 3528, 10404, 30250, 87131, 248832` |
| `padd`, `pmul` | exact integer polynomial addition / multiplication on coefficient lists |
| `char_factor` | `x³ − 2x² − 2x + 1 = (x+1)(x² − 3x + 1)` |
| `char_square` | `(x³ − 2x² − 2x + 1)² = x⁶ − 4x⁵ + 10x³ − 4x + 1` |
| `ZS3` | the ring `Z[√3] ≅ Z[t]/(t²−3)`, modelled as pairs `(re, im) ↔ re + im·√3` |
| `alpha`, `alpha_sq` | `α = 2+√3`; `α² = 7+4√3` |
| `alpha_sq_factor` | `α⁴ − 3α² + 1 = 77 + 44√3` |
| `pEval`, `pEval_alpha_sq` | `p(α²) = 2615536 + 1510080√3` |
| `alpha_sq_ne_neg_one` | `α² ≠ −1` |
| `conjecture_00000000462_false` | the packaged refutation: the recurrence together with `p(α²) ≠ 0` and `α² ≠ −1` |

## Proof strategy

The formalisation mirrors the mathematical argument in `main.tex`.

* **Lucas arithmetic.** `M_rec` is derived from the four-step Lucas identity
  `L(m+4) + L m = 3L(m+2)` by rewriting the indices and closing with `omega`.
  `u_rec` combines `M_rec` with the sign rules `s(n+1) = −s n`,
  `s(n+2) = s n`.
* **The six-term recurrence.** The crucial point is the factor `n` in
  `τ(n) = n·u(n)/5`. Writing `c n = n·u(n)`, the identity
  `c(n+6) − 4c(n+5) + 10c(n+3) − 4c(n+1) + c n = n·P(n) + Q(n)` is proved by
  splitting each `(n+k)·u(n+k)` with `Int.add_mul` and then distributing with
  `simp only [Int.mul_add, Int.mul_sub, Int.mul_left_comm]`; `P_zero` and
  `Q_zero` then kill both terms. `τ = c/5` inherits the recurrence through
  `five_mul_tau`.
* **The algebraic obstruction.** `Z[√3]` is modelled as `Int × Int` with
  `(a,b)·(c,d) = (ac+3bd, ad+bc)`; the value `p(α²) = (2615536, 1510080)` is
  computed by kernel evaluation (`decide`). Both coordinates are nonzero, so
  `p(α²) ≠ 0` in `Z[√3]`, and `Z[√3]` embeds in `ℝ` via `√3`, so `p(α²) ≠ 0`
  in `ℝ` as well.

## Scope note

* The Lean project formalises the sequence `τ` through its exact closed form
  `τ(n) = n(L(2n) + 2(−1)^{n+1})/5` and proves that this sequence satisfies
  the six-term recurrence with the stated characteristic polynomial. The
  identification of this closed form with the number of spanning trees of
  `C_n(1,2)` (the matrix-tree / unit-root product computation of
  `main.tex`, §I) is not formalised: it would require the matrix-tree theorem
  and root-of-unity products, which are far outside core Lean. The
  identification is verified exactly, for `5 ≤ n ≤ 60`, by `reproduce.py`
  (exact integer Kirchhoff determinant vs. closed form).
* The `lean4` project deliberately avoids Mathlib, `ring`, `norm_num` and
  `linarith` (none of which are available in the pinned core toolchain), so all
  algebraic manipulations are carried out with `omega`, explicit distributivity
  lemmas, and kernel computation.
* `Check.lean` reports only `propext` and `Quot.sound` for every theorem and no
  `sorryAx`.
