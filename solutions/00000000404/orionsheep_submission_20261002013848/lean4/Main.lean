/-!
# Disproof of TLMC conjecture 00000000404

Conjecture: in the Schur expansion of the plethysm `s_{(2)}[s_{(n)}]`, the
coefficients of even-indexed partitions `ν` are all even.

Counterexample at `n = 2`:
`s_{(2)}[s_{(2)}] = s_{(4)} + s_{(2,2)}` with both coefficients `1` (odd).

Everything is explicit integer arithmetic in the power-sum basis
(`p1111, p211, p31, p22, p4`, scaled by the common denominator 8); all
proofs are `rfl`/`decide` and depend on no axioms (checked by `Check.lean`).
-/

/-- Symmetric functions of total degree 4 in the power-sum basis.
Fields are the coefficients of `p1111, p211, p31, p22, p4`, each scaled by
the common denominator `8` (so the actual coefficient is `field / 8`). -/
structure P4 where
  c1111 : Int
  c211  : Int
  c31   : Int
  c22   : Int
  c4    : Int

/-- Degree-2 symmetric functions in the power-sum basis: `⟨a, b⟩` denotes
`(a·p11 + b·p2) / 2`.  In particular `s₂ = (p11 + p2)/2 = ⟨1, 1⟩`. -/
structure P2 where
  a : Int
  b : Int

/-- Multiplication in the power-sum basis is `p_ρ · p_σ = p_{ρ ++ σ}`, so
`(a·p11 + b·p2)² / 4 = (a²·p1111 + 2ab·p211 + b²·p22) / 4`, i.e. scaled to
denominator 8: `⟨2a², 4ab, 0, 2b², 0⟩`. -/
def sq2 (x : P2) : P4 := ⟨2 * x.a * x.a, 4 * x.a * x.b, 0, 2 * x.b * x.b, 0⟩

/-- Adams / plethytic operation `ψ²`: `p_k ↦ p_{2k}`, hence
`ψ²((a·p11 + b·p2)/2) = (a·p22 + b·p4)/2`, scaled to denominator 8:
`⟨0, 0, 0, 4a, 4b⟩`. -/
def psi2 (x : P2) : P4 := ⟨0, 0, 0, 4 * x.a, 4 * x.b⟩

/-- Componentwise addition (denominator 8). -/
def add4 (x y : P4) : P4 :=
  ⟨x.c1111 + y.c1111, x.c211 + y.c211, x.c31 + y.c31, x.c22 + y.c22,
    x.c4 + y.c4⟩

/-- Componentwise halving; every component occurring below is even, so the
division is exact. -/
def half4 (x : P4) : P4 :=
  ⟨x.c1111 / 2, x.c211 / 2, x.c31 / 2, x.c22 / 2, x.c4 / 2⟩

/-- The λ-ring identity for the second symmetric power:
`s₂[f] = (f·f + ψ²(f)) / 2` in the power-sum basis (denominator 8). -/
def s2Pleth (x : P2) : P4 := half4 (add4 (sq2 x) (psi2 x))

/-- Substituting `f = s₂ = (p11 + p2)/2`:

`s₂[s₂] = ((p11 + p2)²/4 + (p22 + p4)/2) / 2
        = (p1111 + 2·p211 + 3·p22 + 2·p4) / 8`. -/
theorem attack_expansion : s2Pleth ⟨1, 1⟩ = ⟨1, 2, 0, 3, 2⟩ := rfl

/-- Character table of `S₄`, used for Schur extraction.  Rows are indexed by
the partition `ν` (row `0` = `(4)`, `1` = `(3,1)`, `2` = `(2,2)`,
`3` = `(2,1,1)`, `4` = `(1,1,1,1)`) and columns by the cycle type `ρ`
(col `0` = `(1,1,1,1)`, `1` = `(2,1,1)`, `2` = `(3,1)`, `3` = `(2,2)`,
`4` = `(4)`).  The values agree entry-by-entry with the Murnaghan–Nakayama
computation in `reproduce.py`. -/
def chi4 : Nat → Nat → Int
  | 0, _ => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => -1
  | 1, 4 => -1
  | 2, 0 => 2
  | 2, 1 => 0
  | 2, 2 => -1
  | 2, 3 => 2
  | 2, 4 => 0
  | 3, 0 => 3
  | 3, 1 => -1
  | 3, 2 => 0
  | 3, 3 => -1
  | 3, 4 => 1
  | 4, 0 => 1
  | 4, 1 => -1
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => -1
  | _, _ => 0

/-- Weighted column inner product `Σ_ρ |class(ρ)| · χ^ν_ρ · χ^μ_ρ` with class
sizes `(1, 6, 8, 3, 6)` (`= 4!/z_ρ` for `z_ρ = (24, 4, 3, 8, 4)`). -/
def inner4 (nu mu : Nat) : Int :=
  1 * chi4 nu 0 * chi4 mu 0 + 6 * chi4 nu 1 * chi4 mu 1 +
    8 * chi4 nu 2 * chi4 mu 2 + 3 * chi4 nu 3 * chi4 mu 3 +
    6 * chi4 nu 4 * chi4 mu 4

/-- Sanity check that the table above really is the `S₄` character table:
column orthogonality `Σ_ρ |class(ρ)| χ^ν_ρ χ^μ_ρ = 24·δ_{νμ}` holds for all
`25` pairs `(ν, μ)`. -/
theorem character_table_orthogonal :
    ((List.range 5).all fun i => (List.range 5).all fun j =>
      inner4 i j == if i == j then (24 : Int) else 0) = true := by
  decide

/-- Numerator (times 8) of the Schur coefficient of `ν` in `s₂[s₂]`:
Hall orthogonality gives `c_ν = ⟨f, s_ν⟩ = Σ_ρ a_ρ · χ^ν_ρ` where
`a = (1, 2, 0, 3, 2)/8` is the power-sum vector of
`s₂[s₂] = (p1111 + 2p211 + 3p22 + 2p4)/8` (from `attack_expansion`), so
`8·c_ν = 1·χ^ν_{1111} + 2·χ^ν_{211} + 0·χ^ν_{31} + 3·χ^ν_{22} + 2·χ^ν_4`. -/
def schurNum8 (nu : Nat) : Int :=
  1 * chi4 nu 0 + 2 * chi4 nu 1 + 0 * chi4 nu 2 + 3 * chi4 nu 3 + 2 * chi4 nu 4

/-- The Schur coefficient itself (the numerators are divisible by 8). -/
def schurCoef (nu : Nat) : Int := schurNum8 nu / 8

/-- **The attack.**  At `n = 2` the Schur expansion of `s₂[s₂]` is

* `c_{(4)} = 1` (ODD), `c_{(3,1)} = 0`, `c_{(2,2)} = 1` (ODD),
  `c_{(2,1,1)} = 0`, `c_{(1,1,1,1)} = 0`,

i.e. `s_{(2)}[s_{(2)}] = s_{(4)} + s_{(2,2)}`.  Under every natural reading
of "even-indexed ν" there is an odd coefficient:

* `|ν|` even: `ν = (4)` (or `(2,2)`) has coefficient `1`;
* all parts even: both `(4)` and `(2,2)` have coefficient `1`;
* first part even: `(4)` (and `(2,2)`) have coefficient `1`;
* even length: `ν = (2,2)` has coefficient `1`.

Hence conjecture 00000000404 is **false**. -/
theorem conjecture_404_false :
    schurCoef 0 = 1 ∧ schurCoef 1 = 0 ∧ schurCoef 2 = 1 ∧
      schurCoef 3 = 0 ∧ schurCoef 4 = 0 ∧
      schurCoef 0 % 2 = 1 ∧ schurCoef 2 % 2 = 1 := by
  decide

/-- The two nonzero coefficients are odd (`1 % 2 = 1`). -/
theorem parity_odd : schurCoef 0 % 2 = 1 ∧ schurCoef 2 % 2 = 1 := by
  decide

/-- Weyl dimension cross-check for `GL₄`: `dim Sym²(Sym² ℂ⁴) = C(11,2) = 55`,
`dim S_{(4)} ℂ⁴ = C(7,4) = 35` and `dim S_{(2,2)} ℂ⁴ = 20`; the multiplicities
`(1, 1)` found above match the dimension count `55 = 35 + 20`. -/
theorem dim_check :
    (11 * 10 / 2 : Nat) = 55 ∧
      (7 * 6 * 5 * 4 / (4 * 3 * 2 * 1) : Nat) = 35 ∧
      55 = 35 + 20 := by
  decide

/-- Boundary case `n = 1`: `s₂[s₁] = (p1·p1 + ψ²(p1))/2 = (p11 + p2)/2 = s₂`.
Degree-2 Schur extraction uses `χ^{(2)} = (1, 1)`, `χ^{(1,1)} = (1, -1)` over
`(p11, p2)` with `a = (1/2, 1/2)` (scaled by 2): `2·c_{(2)} = 1 + 1`, so
`c_{(2)} = 1` (odd) and `2·c_{(1,1)} = 1 - 1 = 0`.  The witness `ν = (2)` has
even size, all parts even and first part even — so the conjecture already
fails at `n = 1`; the failure is not an `n = 2` accident. -/
theorem boundary_n1 :
    ((1 * 1 + 1 * 1 : Int) / 2) = 1 ∧
      ((1 * 1 + 1 * -1 : Int) / 2) = 0 ∧
      ((1 * 1 + 1 * 1 : Int) / 2) % 2 = 1 := by
  decide
