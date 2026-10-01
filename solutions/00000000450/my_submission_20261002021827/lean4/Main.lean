/-!
# Disproof of TLMC conjecture 00000000450 (q,t-Catalan at roots of unity)

Conjecture: for the q,t-Catalan number `C_n(q,t)` and every primitive n-th
root of unity ζ,  `C_n(ζ, ζ^{-1}) = (n+1)^((n-1)/2)`.

Standard reading of `C_n(q,t)` (dinv-area form, Garsia-Haiman / Haglund):
`C_n(q,t) = Σ_{D ∈ Dyck_n} q^{area D} t^{dinv D}`, with Dyck paths of
semilength n encoded by area sequences `a = (a_1..a_n)`, `a_1 = 0`,
`0 ≤ a_{i+1} ≤ a_i + 1`, and

* `area D = Σ a_i`
* `dinv D = #{i<j : a_i = a_j} + #{i<j : a_i = a_j + 1}`

At `q = ζ, t = ζ^{-1}` every monomial collapses to `ζ^(area D - dinv D)`,
an exact cyclotomic integer (we work in `Z[ζ]/(Φ_n)` coefficient vectors).

Everything below is core Lean 4 (no Mathlib).  All results are proved by
pure kernel computation (`rfl`/`decide`); `lean4/Check.lean` verifies that
none of them depends on any axiom.
-/

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/-! ## Dyck paths as area sequences -/

/-- Concat-map on lists of lists (avoids relying on `List.flatMap`). -/
def concatMapL {α β : Type} (f : α → List β) (l : List α) : List β :=
  l.foldr (fun x acc => f x ++ acc) []

/-- One refinement step: append every allowed next entry `v` with
    `0 ≤ v ≤ a_n + 1`, where `a_n` is the current last entry. -/
def ext (pre : List Nat) : List (List Nat) :=
  (List.range (pre.getLast! + 2)).map (fun v => pre ++ [v])

/-- All area sequences of Dyck paths of semilength `n`, by refinement steps
    (the first entry is forced to be `0`). -/
def seqsAux : Nat → List (List Nat) → List (List Nat)
  | 0, acc => acc
  | k + 1, acc => seqsAux k (concatMapL ext acc)

/-- The Dyck paths of semilength `n`, as area sequences. -/
def seqs (n : Nat) : List (List Nat) := seqsAux (n - 1) [[0]]

/-- The area statistic: `area D = Σ a_i`. -/
def areaStat (a : List Nat) : Nat := a.foldr (· + ·) 0

/-- The dinv statistic: primary pairs `a_i = a_j` plus secondary pairs
    `a_i = a_j + 1`, over `i < j`. -/
def dinvStat : List Nat → Nat
  | [] => 0
  | x :: xs =>
    (xs.filter (fun y => y == x)).length +
      (xs.filter (fun y => y + 1 == x)).length + dinvStat xs

/-- Exponent of ζ in the term of path `a` at `(ζ, ζ^{-1})`. -/
def expo (a : List Nat) : Int := areaStat a - dinvStat a

/-! ## Cyclotomic integer coefficients

`Z2 c₁ c₂` is `c₁ + c₂·ω` for the quadratic cases below; `Z4` is the
degree-4 basis `1, ω, ω², ω³` for the quintic case.
-/

abbrev Z2 := Int × Int
abbrev Z4 := Int × Int × Int × Int

def add2 (p q : Z2) : Z2 := (p.1 + q.1, p.2 + q.2)
def add4 (p q : Z4) : Z4 :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2.1 + q.2.2.1, p.2.2.2 + q.2.2.2)

/-- Powers of ω, a primitive cube root (`Φ₃(ω) = 0`, so `ω² = −1 − ω`). -/
def wpow (e : Int) : Z2 :=
  match e % 3 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | _ => (-1, -1)

/-- Powers of i, a primitive fourth root (`Φ₄(i) = 0`, so `i² = −1`). -/
def ipow (e : Int) : Z2 :=
  match e % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | _ => (0, -1)

/-- Powers of ζ₅, a primitive fifth root (`Φ₅(ζ₅) = 0`, so
    `ζ₅⁴ = −1 − ζ₅ − ζ₅² − ζ₅³`). -/
def fpow (e : Int) : Z4 :=
  match e % 5 with
  | 0 => (1, 0, 0, 0)
  | 1 => (0, 1, 0, 0)
  | 2 => (0, 0, 1, 0)
  | 3 => (0, 0, 0, 1)
  | _ => (-1, -1, -1, -1)

/-- Powers of ζ₆, a primitive sixth root (`Φ₆(ζ₆) = 0`, so
    `ζ₆² = ζ₆ − 1`). -/
def spow (e : Int) : Z2 :=
  match e % 6 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 1)
  | 3 => (-1, 0)
  | 4 => (0, -1)
  | _ => (1, -1)

/-- Sum of `f a` over all Dyck paths of semilength `n`. -/
def sumOver {β : Type} (n : Nat) (f : List Nat → β) (zero : β)
    (add : β → β → β) : β :=
  (seqs n).foldr (fun a acc => add (f a) acc) zero

/-! ## The attacks -/

/-! ### n = 2:  `C_2(q,t) = q + t`, so `C_2(−1,−1) = −2` (claim: √3) -/

/-- Sign of `(−1)^e`, i.e. the value of `ζ^e` at the primitive 2nd root ζ = −1. -/
def sgn (e : Int) : Int := if e % 2 == 0 then 1 else -1

/-- `C_2(−1,−1)`. -/
def C2 : Int := sumOver 2 (fun a => sgn (expo a)) 0 (· + ·)

theorem C2_eq : C2 = -2 := rfl

theorem C2_ne_sqrt3_sq : (-2 : Int) * (-2 : Int) = 4 := rfl

theorem four_ne_three : (4 : Int) ≠ 3 := by decide

/-! ### n = 3:  `C_3(ζ, ζ^{-1}) = 2` (claim: 4) -/

/-- `C_3(ζ, ζ^{-1})` in `Z[ω]/(Φ₃)`. -/
def C3 : Z2 := sumOver 3 (fun a => wpow (expo a)) (0, 0) add2

theorem C3_eq : C3 = (2, 0) := rfl

theorem two_ne_four : (2 : Int) ≠ 4 := by decide

theorem C3_ne_claim : C3 ≠ (4, 0) := by
  rw [C3_eq]
  decide

/-! ### n = 4:  `C_4(i, i^{-1}) = −2` (claim: 5^{3/2}, irrational) -/

/-- `C_4(i, i^{-1})` in `Z[i]/(Φ₄)`. -/
def C4 : Z2 := sumOver 4 (fun a => ipow (expo a)) (0, 0) add2

theorem C4_eq : C4 = (-2, 0) := rfl

/-! ### n = 5:  `C_5(ζ, ζ^{-1}) = 2` (claim: 36) -/

/-- `C_5(ζ, ζ^{-1})` in `Z[ζ₅]/(Φ₅)`. -/
def C5 : Z4 := sumOver 5 (fun a => fpow (expo a)) (0, 0, 0, 0) add4

theorem C5_eq : C5 = (2, 0, 0, 0) := rfl

theorem two_ne_36 : (2 : Int) ≠ 36 := by decide

theorem C5_ne_claim : C5 ≠ (36, 0, 0, 0) := by
  rw [C5_eq]
  decide

/-! ### n = 6:  `C_6(ζ₆, ζ₆^{-1}) = −2` (claim: 7^{5/2}, irrational) -/

/-- `C_6(ζ₆, ζ₆^{-1})` in `Z[ζ₆]/(Φ₆)`. -/
def C6 : Z2 := sumOver 6 (fun a => spow (expo a)) (0, 0) add2

theorem C6_eq : C6 = (-2, 0) := rfl

/-! ### Boundary: n = 1 satisfies the conjecture -/

theorem C1_eq : sumOver 1 (fun a => wpow (expo a)) (0, 0) add2 = (1, 0) := rfl

/-! ### Sanity: the enumerator really enumerates Dyck paths (Catalan counts) -/

theorem count2 : (seqs 2).length = 2 := rfl
theorem count3 : (seqs 3).length = 5 := rfl
theorem count4 : (seqs 4).length = 14 := rfl
theorem count5 : (seqs 5).length = 42 := rfl

/-- The n = 2 paths themselves: (0,0) [UDUD] and (0,1) [UUDD]. -/
theorem seqs2_val : seqs 2 = [[0, 0], [0, 1]] := rfl

/-- Their statistics: `C_2(q,t) = q^{area} t^{dinv}` terms `q^0 t^1 + q^1 t^0 = q + t`. -/
theorem C2_poly : (seqs 2).map (fun a => (areaStat a, dinvStat a)) =
    [(0, 1), (1, 0)] := rfl
