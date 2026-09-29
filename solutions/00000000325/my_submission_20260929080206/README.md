# Disproof of TLMC Conjecture 00000000325

**Verdict: FALSE.**

## Conjecture

With `W(τ) = {α : liminf q^{1/τ}‖qα‖ = 0}`, the conjecture asserts that the
packing dimension of `W(τ)` equals exactly `2/(1+τ)`.

## Attack

**Primary counterexample: τ = 1/2.** The conjectured value is

    2/(1 + 1/2) = 4/3 > 1,

which exceeds the ambient dimension of R. Packing dimension is monotone and
`dim_P(R) = 1`, so no subset of R can have packing dimension 4/3 — the
conjecture fails outright at τ = 1/2.

Second, independent reason at the same τ: with v = 1/τ = 2, Khintchine's
divergence test requires `Σ q·q^{-v} = Σ 1/q` (harmonic series), which
diverges, so `W(1/2)` has full Lebesgue measure and packing dimension 1 —
already different from 4/3.

## Boundary

For τ = p/q the conjectured value is 2q/(p+q):

- `0 < τ < 1` (q > p): claimed value `2q/(p+q) > 1` since `2q > p+q ⇔ q > p`
  — impossible on the whole range; the conjecture is false for every
  `0 < τ < 1`.
- `0 < τ < 1/2` (v = 1/τ > 2): true value (Jarník–Besicovitch) is
  `2/(v+1) = 2τ/(1+τ)` ≠ `2/(1+τ)` unless τ = 1 (e.g. τ = 1/4: true 2/5,
  claimed 8/5).
- `τ ≥ 1/2` (v ≤ 2): Khintchine gives full measure, true packing dimension
  is 1, while the claim `2/(1+τ)` differs from 1 at every τ ≠ 1 (e.g. τ = 2:
  true 1, claimed 2/3).
- `τ = 1` is the only non-false point (claim 1 = true value 1).

Root cause: `2/(1+τ)` is the classical Jarník value for the normalization
`q^{τ}‖qα‖`, but the conjecture's definition uses `q^{1/τ}` — the
parametrizations are swapped.

## Files

- `main.tex`, `build/main.pdf`, `build/log.txt` — write-up (compiled with
  tectonic).
- `reproduce.py` — standalone exact-rational recomputation
  (`python3 reproduce.py`).
- `lean4/` — core Lean 4 machine verification (no Mathlib). `Main.lean`
  formalizes the arithmetic core (`Tlmc325.attack`: 4/3 > 1; general form
  `Tlmc325.claimed_exceeds_ambient`; mismatch cases τ = 2, τ = 1/4).
  Build with `lake build`; `lake env lean Check.lean` prints
  *does not depend on any axioms* for every declaration — zero axioms,
  zero `sorry`.

## Reproduce

```sh
python3 reproduce.py
cd lean4 && lake build && lake env lean Check.lean
```
