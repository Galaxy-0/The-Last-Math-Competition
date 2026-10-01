# Disproof of TMC Conjecture 00000000433

**Verdict: FALSE** (disproof by counterexample at B₂; pipeline verdict: CONFIRMED)

## The conjecture

Macdonald's denominator identity expresses the denominator of an affine Lie
algebra as a linear combination of monomials; let `T(type)` denote its number
of terms. Conjecture: `T(B_n) = T(C_n) = n`, `T(D_n) = 2n`, `T(G₂) = 2`,
`T(F₄) = 4`, `T(E₆) = 6`, `T(E₇) = 7`, `T(E₈) = 8`; and the number of terms
always equals the multiplicity of exponent 1 in the root system.

## The attack (B₂, killing `T(B₂) = n = 2`)

Macdonald's Weyl denominator formula reads (finite-type RHS of the affine
denominator identity)

    ∏_{α ∈ Δ⁺} (1 − e^{−α})  =  Σ_{w ∈ W} ε(w) e^{w(ρ) − ρ},      ρ = ½ Σ_{α∈Δ⁺} α.

The number of monomial terms on the right equals the number of *distinct*
values of `w(ρ) − ρ` (coefficients are ±1, so terms with different exponents
can never merge or cancel).

For B₂ in the orthonormal realization `Δ = {±e₁, ±e₂, ±e₁ ± e₂}` with positive
system `Δ⁺ = {e₁, e₂, e₁ − e₂, e₁ + e₂}`:

- `ρ = ½(e₁ + e₂ + (e₁ − e₂) + (e₁ + e₂)) = (3/2, 1/2)`;
- `W(B₂)` = the 8 signed coordinate permutations `x ↦ (±x_{σ(1)}, ±x_{σ(2)})`.

The 8 values of `w(ρ) − ρ` are:

| w | w(ρ) − ρ |
|---|---|
| id | (0, 0) |
| (x₁,x₂) ↦ (−x₁, x₂) | (−3, 0) |
| (x₁,x₂) ↦ (x₁, −x₂) | (0, −1) |
| (x₁,x₂) ↦ (−x₁, −x₂) | (−3, −1) |
| (x₁,x₂) ↦ (x₂, x₁) | (−1, 1) |
| (x₁,x₂) ↦ (−x₂, x₁) | (−2, 1) |
| (x₁,x₂) ↦ (x₂, −x₁) | (−1, −2) |
| (x₁,x₂) ↦ (−x₂, −x₁) | (−2, −2) |

All 8 are pairwise distinct (ρ is strictly dominant, hence has trivial
stabilizer, so `w(ρ) = w′(ρ) ⟺ w = w′`). Therefore the denominator identity
of B₂ has exactly **8 monomial terms: T(B₂) = 8 ≠ 2 = n.**

Cross-check (independent realization): in simple-root coordinates of B₂
(α₁ short, Cartan [[2,−2],[−1,2]], reflections `s₁(a,b) = (−a+2b, b)`,
`s₂(a,b) = (a, a−b)`, `ρ = 2α₁ + (3/2)α₂`, integral stand-in `2ρ = (4,3)`)
the 8 values `w(2ρ) − 2ρ` are again pairwise distinct:
`(0,0), (−2,0), (0,−2), (−6,−2), (−2,−4), (−8,−4), (−6,−6), (−8,−6)`,
with the sanity checks `w₀(2ρ) = −2ρ` and `Σ_w (w(2ρ) − 2ρ) = −8·(4,3)`.

Consistency with the pipeline: this recomputation reproduces the f_verify
verdict list `(0,0),(0,−1),(−3,0),(−3,−1),(−1,1),(−1,−2),(−2,1),(−2,−2)`
exactly (orthonormal realization), and both realizations agree on the count.

## Boundary / generality of the failure

The attack is not an edge case — the conjecture fails for **every** root
system it mentions. Since ρ is always strictly dominant, the stabilizer is
trivial and the `|W|` exponents `w(ρ) − ρ` are pairwise distinct, whence
`T(type) = |W(type)|` with no cancellations:

| type | conjectured T | actual T = |W| |
|---|---|---|
| B₁ (= A₁ = C₁) | 1 | 2 |
| B₂ | 2 | 8 |
| Bₙ (n ≥ 3) | n | 2ⁿ·n! |
| Cₙ | n | 2ⁿ·n! |
| Dₙ | 2n | 2ⁿ⁻¹·n! |
| G₂ | 2 | 12 |
| F₄ | 4 | 1152 |
| E₆ | 6 | 51840 |
| E₇ | 7 | 2903040 |
| E₈ | 8 | 696729600 |

Even n = 1 already fails: T(B₁) = 2 ≠ 1. The companion clause "number of
terms = multiplicity of exponent 1" also fails: for B₂ the exponents are
{1, 3}, so the multiplicity of exponent 1 is 1 ≠ 8 = T(B₂).

## Machine verification

- `reproduce.py` — standalone exact-rational recomputation (both realizations
  above); exits non-zero on any mismatch. Run: `python3 reproduce.py`.
- `lean4/` — core-Lean (no Mathlib) formalization of the 8 exponents and
  their pairwise distinctness. Build: `lake build && lake env lean Check.lean`.
  **All theorems are axiom-free** (`#print axioms` reports "does not depend
  on any axioms" for every theorem; no `sorry`, no `native_decide`).
- `build/main.pdf` — compiled write-up (`tectonic main.tex --outdir build`),
  build log in `build/log.txt`.

## Conclusion

Conjecture 00000000433 is **FALSE**: T(B₂) = 8, not 2.
