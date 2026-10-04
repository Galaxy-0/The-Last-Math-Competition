# Disproof of conjecture `00000000462`

**Verdict: FALSE.**

Let `τ(n)` be the number of spanning trees of the circulant graph `C_n(1,2)`,
the *square of the n-cycle*: the graph on `Z/n` joining `i` to `i±1` and `i±2`.
We compute `τ` exactly and show that the conjecture's claimed characteristic
root `α² = (2+√3)² = 7+4√3` is impossible:

* `τ` satisfies the six-term linear recurrence
  `τ(n+6) = 4τ(n+5) − 10τ(n+3) + 4τ(n+1) − τ(n)`, whose characteristic
  polynomial is
  `p(x) = x⁶ − 4x⁵ + 10x³ − 4x + 1 = ((x+1)(x²−3x+1))²`;
* the largest real root of `p` is `φ² = (3+√5)/2 = 2.6180339887…`, not `α²`;
* and `α² = 7+4√3` is **not a root of `p` at all**: an exact computation in
  `Z[√3]` gives

  ```
  p(7 + 4√3) = 2615536 + 1510080·√3 ≠ 0.
  ```

Hence no linear recurrence satisfied by `τ` can have `α²` as a characteristic
root, and the exponential growth rate of `τ` is `φ² = 2.618…`, which differs
from `α² = 13.928…` by a factor of more than five. The conjecture fails under
either reading of its wording (see *The two readings* below).

## The conjecture

Quoted verbatim from `conjectures/00000000462.md`:

> **English.** Definition: τ(circulant C_n(1,2)). Conjecture: τ(C_n(1,2))
> satisfies a linear recurrence whose largest real characteristic root tends to
> α², where α = 2+√3 (directly verifiable against the matrix-tree theorem, then
> stateable in closed form).
>
> **中文。** 定义：τ(circulant C_n(1,2))。猜想：τ(C_n(1,2)) 满足线性递推且其特征根中最大实根 → α²，α = (2+√3)（可与矩阵树直接验证后闭式陈述）。

### Definitions the statement leaves implicit

* **The graph.** For `n ≥ 5`, `C_n(1,2)` is the circulant graph on `Z/nZ` in
  which `i` and `j` are adjacent iff `j−i ≡ ±1` or `j−i ≡ ±2 (mod n)`.
  For `n = 3` and `n = 4` the connection set `{±1, ±2}` collapses and the graph
  is `K_3` resp. `K_4` with `τ(3) = 3`, `τ(4) = 16`; every statement below
  concerns the general case `n ≥ 5`, which is what the conjecture is about.
* **`τ(G)`.** The number of spanning trees of `G`.
* **Lucas numbers.** `L(0) = 2`, `L(1) = 1`, `L(k+2) = L(k+1) + L(k)`.
* **Characteristic root.** For a linear recurrence
  `a_{n+k} = c_{k−1}a_{n+k−1} + … + c_0a_n`, the characteristic roots are the
  roots of `x^k − c_{k−1}x^{k−1} − … − c_0`; equivalently, the roots of any
  annihilating polynomial of the sequence. (This is the standard meaning, and
  the only one under which the conjecture's phrase "largest real characteristic
  root" is well-defined.)

## I. The exact spanning-tree count

**Theorem.** For every `n ≥ 5`,

```
τ(n) = n·(L(2n) + 2·(−1)^(n−1)) / 5.
```

*Proof sketch (full details in `main.tex`).* By the matrix-tree theorem,
`τ = (1/n)·∏_{k=1}^{n−1} λ_k` where, for a circulant graph with connection set
`S`, `λ_k = Σ_{s∈S}(1 − ω^{ks})`, `ω = e^{2πi/n}`. With `S = {±1, ±2}` and
`z = ω^k`,

```
λ_k = 4 − z − z^{-1} − z² − z^{-2} = −(z−1)²(z²+3z+1)/z²,
```

using `z⁴ + z³ − 4z² + z + 1 = (z−1)²(z²+3z+1)`. The product over the
nontrivial `n`-th roots of unity evaluates by the standard root-of-unity
identities:

* `∏_{k=1}^{n−1}(z_k − 1) = (−1)^{n−1}·n`, hence `∏(z_k−1)² = n²`;
* `∏ z_k² = 1`;
* with `r_1, r_2` the roots of `z²+3z+1` (so `r_1+r_2 = −3`, `r_1r_2 = 1`,
  `(r_1−1)(r_2−1) = 5`),
  `∏(z_k²+3z_k+1) = (r_1^n−1)(r_2^n−1)/5`.

Putting these together, `τ(n) = (−1)^{n−1}·n·(r_1^n−1)(r_2^n−1)/5`. Writing
`s_1 = (3−√5)/2`, `s_2 = (3+√5)/2`, we have `r_1 = −s_1`, `r_2 = −s_2`, and
`s_1^n + s_2^n = L(2n)`, so `(r_1^n−1)(r_2^n−1) = 2 − (−1)^n L(2n)` and the
displayed formula follows. ∎

The integrality statement `5 | L(2n) + 2(−1)^{n−1}` is immediate:
`L(2n) ≡ 2 (mod 5)` for even `n` and `≡ 3 (mod 5)` for odd `n`.

**First values** (all cross-checked against the exact integer Kirchhoff
determinant in `reproduce.py`):

| `n` | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|:--|--:|--:|--:|--:|--:|--:|--:|--:|
| `τ(n)` | 125 | 384 | 1183 | 3528 | 10404 | 30250 | 87131 | 248832 |

## II. The recurrence and its characteristic polynomial

Put `u(n) = L(2n) + 2(−1)^{n−1}`, so that `τ(n) = n·u(n)/5`.

* **The recurrence for `u`.** The even-index Lucas numbers satisfy
  `L(2n+4) = 3L(2n+2) − L(2n)` (characteristic polynomial `x²−3x+1`), and
  `(−1)^{n−1}` satisfies `x+1`. Hence `u` satisfies
  `(E²−3E+1)(E+1)u = 0`, i.e.

  ```
  u(n+3) = 2·u(n+2) + 2·u(n+1) − u(n),        q(x) = x³ − 2x² − 2x + 1
        = (x+1)(x² − 3x + 1).
  ```

* **The recurrence for `τ`.** Multiplying a sequence satisfying `q(E)w = 0` by
  `n` doubles every root, so `q(E)²(n·w) = 0`. With `w = u` and
  `τ = n·u/5` this gives `p(E)τ = 0` for

  ```
  p(x) = q(x)² = (x³ − 2x² − 2x + 1)² = x⁶ − 4x⁵ + 10x³ − 4x + 1
       = ((x+1)(x² − 3x + 1))²,
  ```

  i.e. the six-term recurrence displayed in the verdict. The factorisation is
  verified by exact integer polynomial multiplication in both `reproduce.py`
  and the Lean project.

* **The roots.** `−1` (double) and `(3±√5)/2` (each double). The largest real
  root is

  ```
  φ² = (3+√5)/2 = 2.6180339887…,
  ```

  and indeed `τ(n) ~ n·φ^{2n}/5`, so `lim τ(n)^{1/n} = φ²`.

## III. The conjectured root is not a characteristic root

**Theorem.** `α² = (2+√3)² = 7+4√3` is not a root of
`p(x) = x⁶ − 4x⁵ + 10x³ − 4x + 1`.

*Proof.* Since `p(x) = (x+1)²(x²−3x+1)²`, a number is a root of `p` iff it is
`−1` or a root of `x²−3x+1`. Work in `Z[√3] ≅ Z[t]/(t²−3)`. With `α = 2+√3`,

```
α² = 7 + 4√3,      α⁴ = (α²)² = 97 + 56√3,
α⁴ − 3α² + 1 = (97+56√3) − 3(7+4√3) + 1 = 77 + 44√3 ≠ 0,
α² = 7+4√3 ≠ −1.
```

Therefore

```
p(α²) = (α²+1)²·(α⁴−3α²+1)² = (8+4√3)²·(77+44√3)²
      = 2615536 + 1510080·√3 ≠ 0. ∎
```

**Corollary (refutation).** Every characteristic root of `τ` is a root of `p`
(the minimal annihilator divides any annihilator), and `α²` is not a root of
`p`. Hence `α²` is not a characteristic root of any linear recurrence satisfied
by `τ`. The conjecture is false.

## The two readings of the conjecture

The filed wording says the largest real characteristic root "tends to" `α²`.
"Tends to" is not standard for characteristic roots of a constant-coefficient
recurrence, so we dispose of both natural readings.

1. **"Characteristic root" = root of the characteristic polynomial.** Every
   characteristic root of `τ` is a root of `p`, and `α²` is not one.
   *False.*
2. **"Tends to" = the exponential growth rate is `α²`.** The limit
   `lim τ(n)^{1/n}` is `φ² = 2.6180339887…`, not `α² = 13.9282032302…`.
   *False.* (For `n = 60`, `[τ(60)/60] / [τ(59)/59] = 2.6180339887` to ten
   decimal places.)

`α = 2+√3` is unrelated to `C_n(1,2)`: in particular `α` is not `φ^k` for any
integer `k` (`φ³ = 2+√5`), so it cannot arise from the Lucas family that
actually governs `τ`.

## Numerical vantage point

| quantity | value | status |
|:--|:--|:--|
| `φ² = (3+√5)/2` | `2.6180339887…` | root of `p`; the actual growth rate |
| `α² = 7+4√3` | `13.9282032302…` | **not** a root; `p(α²) = 2615536 + 1510080√3` |

## Files

| File | Description |
|:--|:--|
| `README.md` | This document: verdict, quoted conjecture, the closed form, the recurrence, the root computation, both readings, reproduction, status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`; compiles with `tectonic main.tex`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only, exact integer arithmetic): matrix-tree determinant for `5 ≤ n ≤ 60`, the closed form, integrality, the six-term recurrence, the factorisation, and the exact `Z[√3]` computation. Prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; project `tlmc462`, library `Main`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation, core Lean only (`import Std`, no Mathlib, no `sorry`, no `native_decide`): Lucas arithmetic, the recurrences, the factorisation, and the obstruction in `Z[√3]`. |
| `lean4/Trees.lean` | The conjecture's own object: the graph `C_n(1,2)`, its spanning trees by exhaustive enumeration, and the proof that the closed form agrees with the enumeration for `n = 5, 6, 7`. |
| `lean4/Check.lean` | `#print axioms` audit for every theorem in both modules. |
| `lean4/README.md` | Statement tables for both modules, proof strategy, and the scope note / boundary of the formalisation. |

## Reproducing

```sh
python3 reproduce.py
```

Dependency-free, runs in about a third of a second. It evaluates the exact
Kirchhoff determinant by fraction-free Bareiss elimination, checks the closed
form and the integrality statement, checks the six-term recurrence, verifies
`x⁶−4x⁵+10x³−4x+1 = ((x+1)(x²−3x+1))²` by exact integer polynomial
multiplication, and computes `p(7+4√3) = 2615536 + 1510080√3 ≠ 0` in `Z[√3]`.
It prints `PASS` and exits `0` exactly when every check holds.

```sh
tectonic --outdir build main.tex     # produces build/main.pdf
cd lean4 && lake build && lake env lean Check.lean
```

The Lean audit reports only `[propext, Quot.sound]` for the theorems that need
them, **no axioms at all** for the whole spanning-tree enumeration layer
(`Trees.lean`), and no `sorryAx`.

## Boundary of the formalisation

This boundary statement is part of the submission and should be read together
with the formalisation. The same statement appears in `main.tex`
(*Boundary of the formalisation*) and in `lean4/README.md`.

* **Kernel-certified.** The Lucas arithmetic; the three-term recurrence for
  `u(n) = L(2n) + 2(−1)^(n+1)`; the six-term recurrence for `c = n·u` and hence
  for `τ`; the integrality `5 | u(n)`; the initial values `τ(5)…τ(12)`; the
  factorisation `x³−2x²−2x+1 = (x+1)(x²−3x+1)` and its square, as an exact
  identity of integer coefficient lists; the value
  `p(α²) = 2615536 + 1510080√3` in the pair model of `Z[√3]`; and, for
  `n = 5, 6, 7`, the equality of the closed-form sequence with the genuinely
  enumerated spanning-tree count of `C_n(1,2)`.
* **Not formalised, and why.** The general-`n` identification
  “closed form = number of spanning trees of `C_n(1,2)`” rests on two classical
  inputs proved in full in `main.tex` §I: the matrix-tree theorem (Kirchhoff)
  and the evaluation of a product over the nontrivial `n`-th roots of unity.
  Formalising Kirchhoff's theorem for arbitrary connected graphs is far outside
  core Lean and would require substantial Mathlib infrastructure. The identity
  is instead verified exactly and independently for `5 ≤ n ≤ 60` by the integer
  Bareiss determinant in `reproduce.py`, and for `n = 5, 6, 7` it is
  kernel-certified by brute-force enumeration in `Trees.lean`, without
  appealing to Kirchhoff's theorem at all.
* **The logical bridge to “characteristic root”.** The formalisation certifies
  the arithmetic fact `p(α²) ≠ 0`. The step to “`α²` is not a characteristic
  root of any recurrence satisfied by `τ`” uses the standard fact that the
  minimal annihilating polynomial divides every annihilating polynomial. That
  is proved in `main.tex` (Corollary, §III) but not itself formalised: core Lean
  has no polynomial-ring or linear-algebra library. The step is elementary and
  independent of the conjecture.
* **Asymptotics.** `lim τ(n)^{1/n} = φ²` is a real-analysis limit statement and
  is not formalised (core Lean has no reals or limits). It is verified
  numerically to ten decimal places in `reproduce.py`, and it is not needed for
  the refutation, which already follows from the algebraic obstruction.

## Status against the submission rules

Rules for Problem Solvers, rule 1 requires the LaTeX source, a PDF document, a
Lean 4 project, and any auxiliary code; rule 2 requires that the conjecture be
unsolved before opening the pull request; rule 3 requires that the pull request
contain only the personal submission under the problem folder.

* **LaTeX source** — present (`main.tex`), standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `parskip`, `booktabs`, `array`;
  compiles with `tectonic main.tex`.
* **PDF document** — present at `build/main.pdf`.
* **Lean 4 project** — present under `lean4/`: `Main.lean` (Lucas arithmetic,
  the recurrences, the factorisation, the obstruction in `Z[√3]`),
  `Trees.lean` (the graph `C_n(1,2)`, its spanning trees by exhaustive
  enumeration, and the agreement with the closed form for `n = 5, 6, 7`),
  `Check.lean` (axiom audit), `lakefile.toml` (modules `Main` and `Trees`),
  `lean-toolchain`, `README.md`. Core Lean only, no `sorry`, no
  `native_decide`; `lake build` and `lake env lean Check.lean` both succeed.
* **Auxiliary code** — `reproduce.py`, dependency-free, exits `0` with `PASS`.
* **Conjecture unsolved at submission time** — `metadata.csv` records
  `proven=false, disproven=false` for `00000000462`, there is no
  `solutions/00000000462/` directory, and no pull request references it.
* **Nothing else touched** — the pull request adds only
  `solutions/00000000462/earthking11_submission_20261004212700/`.
