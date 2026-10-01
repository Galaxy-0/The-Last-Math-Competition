# Disproof of TLMC conjecture 00000000589

**Verdict: FALSE.**

**Conjecture.** For three-generated numerical semigroups `S = <a,b,c>`,
`g(S) <= sqrt(3) * (abc)^(1/3) * (1 + o(1))`, and the constant `sqrt(3)` is
optimal (Erdos-Graham type), where `g(S)` is the Frobenius number.

**Disproof.** Along the family `S_n = <n, n+1, n^2-n-1>` the Frobenius number
is *exactly* `n^2 - 2n - 1` (proved below and in Lean), so

    g(S_n) / (sqrt(3) * (n(n+1)(n^2-n-1))^(1/3))  ~  n^(2/3) / sqrt(3) -> infinity.

The bound fails from `n = 6` on (first violation: `g(<6,7,29>) = 23` vs
`sqrt(3)*(6*7*29)^(1/3) = 18.497`, ratio 1.2434) and by an unbounded factor
(`n = 20`: ratio 3.8245; `n = 100`: ratio 12.19). No constant can rescue it,
so "`sqrt(3)` is optimal" is false a fortiori.

## Exact statement proved (in Lean, zero axioms)

For every `n >= 3`:

    g(<n, n+1, n^2 - n - 1>) = n^2 - 2n - 1.

*Non-representability of `N = n^2-2n-1`.* If `N = x*n + y*(n+1) + z*(n^2-n-1)`
with `z >= 1` the right side is already `>= n^2-n-1 > N`. If `z = 0`, writing
`x*n + y*(n+1) = (x+y)*n + y` and reducing mod `n` forces `y >= n-1`, while
`y <= x+y <= n-3` follows from `(x+y)*n = N - y <= (n-3)*n` — contradiction.
*Representability of everything `> N`.* Window `[N, n^2-n-2]` is covered by
`(n-2-i)*n + i*(n+1) = N + i` for `0 <= i <= n-2`; the point `n^2-n-1` is the
third generator itself; above it, peel one `n` and induct.

Consequently the ratio `g/(sqrt(3)*(abc)^(1/3))` equals
`(n^2-2n-1)/(sqrt(3)*(n(n+1)(n^2-n-1))^(1/3)) ~ n^(2/3)/sqrt(3) -> infinity`.

## Boundary

- `n = 2`: `n^2-n-1 = 1`, the semigroup is trivial (contains 1); excluded.
- `n = 3,4,5`: bound still holds (ratios 0.295, 0.669, 0.975).
- `n = 6`: first violation (ratio 1.2434).
- Remark: the third generator `n^2-n-1` is exactly `g(<n,n+1>)`; inserting the
  two-generator Frobenius number as third generator only lowers `g` to
  `(n-1)*... = n^2-2n-1`, and the two-generator obstruction `g ~ ab` survives,
  which is what kills any constant bound of the form `C*(abc)^(1/3)`.

## Files

- `main.tex`, `build/main.pdf`, `build/log.txt` — full write-up (tectonic).
- `reproduce.py` — independent recomputation (pure Python, no deps):
  brute-force Frobenius enumeration confirms `g = n^2-2n-1` for all `3 <= n <= 60`,
  ratios, first violation, divergence. Run: `python3 reproduce.py`.
- `lean4/` — Lean 4 verification (toolchain `leanprover/lean4:v4.33.1`, no Mathlib):

```sh
cd lean4
lake build
lake env lean Check.lean
```

Every audited declaration (toolkit, `window`, `repr_shifted`, `repr_ge`,
`notrepr`, `frob_family`, `frob6/20/100`, `cert6/20/100`,
`violation6/20/100`, 31 declarations in total) reports
**"does not depend on any axioms"** — zero `sorryAx`, zero `Classical.choice`,
zero `Quot.sound`, zero `propext`. The core-Nat subtraction lemmas carry
`propext` in this Lean version, so the truncated-subtraction toolkit is
re-derived from scratch by structural induction (`my_*` section of `Main.lean`).

## Root-free violation certificates used in Lean

Because `3*sqrt(3) < 5`, the inequality `5 * abc < g^3` certifies
`g > sqrt(3) * (abc)^(1/3)` for positive `g, abc`:

- `5*1218 = 6090 < 12167 = 23^3` (n = 6),
- `5*159180 = 795900 < 46268279 = 359^3` (n = 20),
- `5*99979900 = 499899500 < 940903909399 = 9799^3` (n = 100).
