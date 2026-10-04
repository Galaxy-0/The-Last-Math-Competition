# Lean 4 formalisation — disproof of conjecture `00000000462`

Core Lean only (`import Std`; **no Mathlib**, no `sorry`, no `native_decide`).

```sh
lake build                     # builds Main and Trees (~95 s, dominated by Trees)
lake env lean Check.lean       # axiom audit
```

Two modules:

* **`Main.lean`** — the Lucas arithmetic, the recurrences, the algebraic
  obstruction in `Z[√3]`, and the packaged refutation.
* **`Trees.lean`** — the conjecture's own object: the graph `C_n(1,2)`, its
  spanning trees by exhaustive enumeration, and the proof that the closed-form
  sequence agrees with that enumeration for `n = 5, 6, 7`.

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
   in `Z[√3] ≅ Z[t]/(t²−3)`, which is nonzero;
4. and, as an explicit finite bridge to the conjecture's own object, that the
   closed-form sequence equals the *actually enumerated* number of spanning
   trees of `C_n(1,2)` for `n = 5, 6, 7`.

Since a characteristic root of a linear recurrence must be a root of every
annihilating polynomial, and `α²` is not a root of `p`, `α²` cannot be a
characteristic root of any recurrence satisfied by `τ`.

## Statement table — `Main.lean`

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

## Statement table — `Trees.lean`

| Lean name | Statement |
|:--|:--|
| `edgesC` | the unordered edge set of `C_n(1,2)`: pairs `i < j` with `j − i ∈ {1, 2, n−1, n−2}` |
| `adj` | `adj S u v`: some edge of `S` joins `u` and `v` |
| `reachFrom` | the vertices reachable from `0` in `k` rounds of the adjacency closure |
| `connected` | `S` connects all `n` vertices |
| `sublists` | the powerset of a list |
| `isSpanningTree` | a subgraph on `n−1` edges connecting all `n` vertices (acyclicity is forced) |
| `spanningTrees` | **all spanning trees of `C_n(1,2)`, by exhaustive enumeration** |
| `edgesC_5`, `edgesC_6`, `edgesC_7` | the edge counts `10`, `12`, `14` |
| `trees_5`, `trees_6`, `trees_7` | `(spanningTrees n).length = 125`, `384`, `1183` |
| `tau_eq_trees_5/6/7` | `τ(n) = (spanningTrees n).length` for `n = 5, 6, 7` |
| `tau_matches_spanningTrees` | the three equalities packaged together |

These last four theorems report **no axioms at all** in `Check.lean`: they are
pure kernel computation.

## Proof strategy

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
* **The brute-force bridge.** `Trees.lean` enumerates all `2^10`, `2^12` and
  `2^14` subgraphs of `C_5(1,2)`, `C_6(1,2)`, `C_7(1,2)` and filters the
  spanning trees, certifying `125`, `384`, `1183`. This needs no matrix-tree
  theorem. The modules are declared in `lakefile.toml` via
  `globs = ["Main", "Trees"]`; the enumeration needs
  `set_option maxRecDepth 1000000` and `maxHeartbeats 0`, and takes about 95
  seconds to elaborate.

## Scope note — boundary of the formalisation

This section is the machine-readable counterpart of the *Boundary of the
formalisation* subsection in `main.tex`; it is part of the submission.

* **Kernel-certified.** All arithmetic and algebra listed in the two statement
  tables above, including: `τ` satisfies the six-term recurrence; the
  factorisation of `p`; `p(α²) ≠ 0` in `Z[√3]`; and, for `n = 5, 6, 7`, the
  equality of the closed-form sequence with the genuinely enumerated
  spanning-tree count of `C_n(1,2)`.
* **Not formalised (and why).** The general-`n` identification
  `closed form = number of spanning trees of C_n(1,2)` rests on two classical
  inputs proved in full in `main.tex` §I: the **matrix-tree theorem**
  (Kirchhoff) and the evaluation of a product over the nontrivial `n`-th roots
  of unity. Formalising Kirchhoff's theorem for arbitrary connected graphs
  (Laplacian determinants, Cauchy–Binet, root-of-unity products) is far outside
  core Lean and would need substantial Mathlib infrastructure. The identity is
  instead verified exactly and independently for `5 ≤ n ≤ 60` by the integer
  Bareiss determinant in `reproduce.py`, and for `n = 5, 6, 7` it is
  kernel-certified by brute force in `Trees.lean` without appealing to
  Kirchhoff at all.
* **The logical bridge to "characteristic root".** The formalisation certifies
  the arithmetic fact `p(α²) ≠ 0`. The step to "`α²` is not a characteristic
  root" uses the standard fact that the minimal annihilating polynomial of a
  linear recurrence divides every annihilating polynomial. That is proved in
  `main.tex` (Corollary, §III) but not formalised: core Lean has no polynomial
  ring or linear algebra library. The step is elementary and independent of the
  conjecture.
* **Asymptotics.** `lim τ(n)^{1/n} = φ²` is a real-analysis limit statement and
  is not formalised (core Lean has no reals or limits). It is verified
  numerically to ten decimal places in `reproduce.py`, and it is not needed for
  the refutation, which already follows from the algebraic obstruction.
* The project deliberately avoids Mathlib, `ring`, `norm_num` and `linarith`
  (none of which are available in the pinned core toolchain), so all algebraic
  manipulations are carried out with `omega`, explicit distributivity lemmas,
  and kernel computation.
* `Check.lean` reports only `propext` and `Quot.sound` for the theorems that
  need them, **no axioms at all** for the entire `Trees.lean` layer, and no
  `sorryAx` anywhere.
