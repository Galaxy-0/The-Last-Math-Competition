# Disproof of TLMC Conjecture 00000000450

**Verdict: FALSE.**

## Conjecture (as stated)

For the q,t-Catalan number `C_n(q,t)` and every relevant root of unity ζ
(a primitive n-th root of unity):

```
C_n(ζ, ζ^{-1}) = (n+1)^((n-1)/2)
```

## Reading of `C_n(q,t)`

The standard q,t-Catalan number (the corpus itself glosses the family at the
neighbouring entry 00000000449 as "Haiman's bisymmetric generalization of the
Catalan numbers"), in the standard dinv-area form (Garsia–Haiman; Haglund):

```
C_n(q,t) = Σ_{D ∈ Dyck_n} q^{area(D)} t^{dinv(D)}
```

where Dyck paths of semilength n are encoded by area sequences
`a = (a_1,…,a_n)`, `a_1 = 0`, `0 ≤ a_{i+1} ≤ a_i + 1` (Catalan-many),

```
area(D) = Σ_i a_i
dinv(D) = #{i<j : a_i = a_j} + #{i<j : a_i = a_j + 1}    (primary + secondary dinv)
```

Sanity checks: `C_2(q,t) = q + t` and `C_3(1,1) = 5` (the Catalan numbers).

At `q = ζ, t = ζ^{-1}` (ζ primitive n-th root, `ζ^n = 1`):

```
C_n(ζ, ζ^{-1}) = Σ_D ζ^{area(D) − dinv(D)}        -- exact cyclotomic integer
```

## Attacks (all values recomputed exactly; both pipeline anchors reproduced)

| n | C_n(ζ, ζ^{-1}) exact (in Z[ζ]/(Φ_n)) | claimed (n+1)^((n−1)/2) | |
|---|---|---|---|
| 1 | 1 | 1 | holds |
| 2 | **−2** (C_2(q,t)=q+t at (−1,−1)) | √3 (irrational) | refuted |
| 3 | **2** (= 3 + ζ + ζ^{-1} = 3 − 1) | 4 | refuted |
| 4 | **−2** (in Z[i]) | 5^{3/2} (irrational) | refuted |
| 5 | **2** | 36 | refuted |
| 6 | **−2** (in Z[ζ_6]) | 7^{5/2} (irrational) | refuted |

Details of the two headline attacks:

- **n = 2.** The two Dyck paths have (area, dinv) = (0,1), (1,0), so
  `C_2(q,t) = q + t` and `C_2(−1,−1) = −2 ≠ 3^{1/2}` (indeed (−2)² = 4 ≠ 3 =
  (√3)², and √3 is irrational while −2 is an integer). This reproduces the
  pipeline anchor "C₂ = q+t; C₂(−1,−1) = −2".
- **n = 3.** The five Dyck paths give exponents area − dinv = −3, 0, −1, 1, 3;
  hence `C_3(ζ, ζ^{-1}) = 3 + (ζ + ζ^{-1}) = 2 ≠ 4`. This reproduces the
  pipeline anchor "C₃(ζ,ζ^{-1}) = 2".
- **n = 5** gives a second integer-vs-integer refutation: 2 ≠ 36.

For odd n both sides are ordinary integers and disagree; for even n the left
side is the algebraic integer ±2 while the right side is irrational
(n + 1 is not a perfect square for 2 ≤ n ≤ 6). The universal claim therefore
fails at every n ≥ 2 tested.

## Boundary

n = 1 is consistent: the unique Dyck path has (area, dinv) = (0,0), so
`C_1(1,1) = 1 = (1+1)^0`.

## Verification

1. **`reproduce.py`** — standalone, stdlib-only, pure integer arithmetic
   (exact cyclotomic reduction mod Φ_n). Run `python3 reproduce.py`.
2. **`main.tex` / `build/main.pdf`** — self-contained writeup
   (built with tectonic; log in `build/log.txt`).
3. **`lean4/`** — core Lean 4 (v4.33.1, no Mathlib) formalization.
   `Main.lean` defines the area-sequence enumerator and both statistics and
   proves by pure kernel computation: `C2 = −2`, `C3 = 2`, `C3 ≠ 4`,
   `C4 = −2`, `C5 = 2`, `C5 ≠ 36`, `C6 = −2`, plus the enumeration counts
   (2, 5, 14, 42 for n = 2..5 — the Catalan numbers, confirming the Dyck
   enumeration) and the n = 2 identity `C_2(q,t) = q + t`.
   `Check.lean` audits every theorem with `#print axioms`: all report
   **"does not depend on any axioms"**.

Rebuild Lean locally:

```
cd lean4
export ELAN_HOME=/Users/mychanging/.workbuddy-ai/binaries/lean/elan
export PATH="$ELAN_HOME/bin:$PATH"
lake build && lake env lean Check.lean
```
