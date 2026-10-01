# Disproof of TLMC Conjecture 00000000485

**Verdict: FALSE.**

## The conjecture

Let `chi_lambda(c_n)` denote the irreducible character of the symmetric group
`S_n` at an n-cycle `c_n`, evaluated at an irreducible representation indexed
by a partition `lambda` of `n`. The conjecture claims that the proportion of
shapes `lambda |- n` with `|chi_lambda(c_n)| > 1` tends to `1` as
`n -> infinity`.

## The attack

By the Murnaghan–Nakayama rule, `chi_lambda(c_n)` is computed by removing a
rim hook of size `n` from the Young diagram of `lambda`. Since `n` is the
total number of boxes, this succeeds **iff the whole diagram of `lambda` is
itself a border strip** (connected, no 2x2 block). For a straight shape this
means exactly that `lambda` is a **hook** (`lambda_2 <= 1`), and then the
value is `(-1)^(height - 1)`; otherwise the value is `0`.

Hence, **for every `n` and every `lambda |- n`**:

```
chi_lambda(c_n) in { -1, 0, +1 }
```

so `#{lambda : |chi_lambda(c_n)| > 1} = 0` identically, and the proportion is
the constant function `0`, which certainly does not tend to `1`. The
conjecture is not merely false — it is maximally false: the quantity it
claims tends to 1 is identically 0. There are no boundary or exceptional
cases; the statement `|chi_lambda(c_n)| <= 1` is unconditional for all `n`
and all `lambda |- n`.

## Verification performed

1. **Independent recomputation** (`reproduce.py`, pure stdlib): characters
   computed by a from-scratch Murnaghan–Nakayama implementation; the
   implementation validated against column orthogonality
   (`sum_lambda chi_lambda(mu)^2 = z_mu` for every `mu |- n`), the
   hook-length formula (`f^lambda = chi_lambda(1^n)`), and the standard
   representation identity `chi_{(n-1,1)}(mu) = (#fixed points) - 1`.
   Result: for `n = 1..15` the n-cycle column consists only of `0, +-1`;
   the count of shapes with `|chi| > 1` is `0` for every `n`
   (e.g. `0/30` at `n=9`, `0/42` at `n=10`, `0/176` at `n=15`).
2. **Lean 4 machine check** (`lean4/`, zero axioms, zero `sorry`): a
   computable model implementing the Murnaghan–Nakayama value at the n-cycle
   (border-strip test + sign), the exact partition enumerations
   (`(parts 10).length = 42`, `(parts 12).length = 77`, all parts summing to
   `n`), and kernel-checked theorems that the number of shapes with
   `|chi| > 1` is `0` for `n = 3..12`. `#print axioms` reports
   *"does not depend on any axioms"* for every listed theorem.

## Files

- `README.md` — this file.
- `main.tex` — full write-up (compiles with `tectonic main.tex --outdir build`).
- `build/main.pdf`, `build/log.txt` — compiled paper and build log.
- `reproduce.py` — standalone recomputation: `python3 reproduce.py`.
- `lean4/` — Lean 4 package (`lake build && lake env lean Check.lean`).

## Conclusion

The proportion of shapes with `|chi_lambda(c_n)| > 1` is identically `0`
(equivalently: `chi_lambda(c_n) in {0, +-1}` for all `lambda |- n`, a
classical consequence of Murnaghan–Nakayama). The conjectured limit
`-> 1` is impossible.
