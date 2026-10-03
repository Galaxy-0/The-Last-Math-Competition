import Std
import Std.Internal.Rat

namespace Conjecture2594
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

instance boolForall (P : Bool → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (P false ∧ P true) Bool.forall_bool.symm

instance productForall {m n} (P : Fin m × Fin n → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (∀ a b, P (a,b)) (by
    constructor
    · intro h x; exact h x.1 x.2
    · intro h a b; exact h (a,b))

def Cover {V : Type} (le : V → V → Bool) (x y : V) : Prop :=
  le x y = true ∧ x ≠ y ∧ ∀ z, le x z = true → le z y = true → z = x ∨ z = y

/-- A finite graded poset, with its full universe, partial-order axioms,
rank normalization, cover increments, and common maximal rank explicit. -/
structure RankedPoset (V : Type) where
  vertices : List V
  nodup : vertices.Nodup
  complete : ∀ x, x ∈ vertices
  le : V → V → Bool
  refl : ∀ x, le x x = true
  antisymm : ∀ x y, le x y = true → le y x = true → x = y
  trans : ∀ x y z, le x y = true → le y z = true → le x z = true
  rank : V → Nat
  height : Nat
  rank_bound : ∀ x, rank x ≤ height
  minimal_rank : ∀ x, (∀ y, le y x = true → y = x) → rank x = 0
  maximal_rank : ∀ x, (∀ y, le x y = true → y = x) → rank x = height
  cover_rank : ∀ x y, Cover le x y → rank y = rank x + 1

def rankSize {V} (P : RankedPoset V) (r : Nat) : Nat :=
  (P.vertices.filter (fun x => decide (P.rank x = r))).length

def Antichain {V} (P : RankedPoset V) (S : V → Bool) : Prop :=
  ∀ x y, S x = true → S y = true → P.le x y = true → x = y

/-- This is the ordinary rational Lubell sum, using Lean's rational type. -/
def lubell {V} (P : RankedPoset V) (S : V → Bool) : Std.Internal.Rat :=
  (P.vertices.map (fun x => if S x then
    (1 : Std.Internal.Rat) / (OfNat.ofNat (rankSize P (P.rank x)) : Std.Internal.Rat) else 0)).sum

def LYM {V} (P : RankedPoset V) : Prop :=
  ∀ S : V → Bool, Antichain P S → lubell P S ≤ 1

/-- Boolean subsets represent every actual subset, including noncomputable
predicates. Thus LYM does not restrict the antichains being quantified over. -/
theorem every_subset_represented {V : Type} (S : V → Prop) :
    ∃ B : V → Bool, ∀ x, B x = true ↔ S x := by
  classical
  exact ⟨fun x => decide (S x), fun x => decide_eq_true_iff⟩

theorem lym_for_every_subset {V} (P : RankedPoset V) (h : LYM P)
    (S : V → Prop) (B : V → Bool) (hB : ∀ x, B x = true ↔ S x)
    (hS : ∀ x y, S x → S y → P.le x y = true → x = y) : lubell P B ≤ 1 := by
  apply h B
  intro x y hx hy hxy
  exact hS x y ((hB x).mp hx) ((hB y).mp hy) hxy

def pRank (x : Fin 5) : Nat := if x.val = 0 then 0 else if x.val = 1 then 1 else 2
def pLE (x y : Fin 5) : Bool := decide (x = y ∨ pRank x < pRank y)

def P : RankedPoset (Fin 5) where
  vertices := List.finRange 5
  nodup := by decide
  complete := by decide
  le := pLE
  refl := by decide
  antisymm := by decide
  trans := by decide
  rank := pRank
  height := 2
  rank_bound := by decide
  minimal_rank := by decide
  maximal_rank := by decide
  cover_rank := by unfold Cover; decide

def qLE (x y : Fin 2) : Bool := decide (x.val ≤ y.val)
def Q : RankedPoset (Fin 2) where
  vertices := List.finRange 2
  nodup := by decide
  complete := by decide
  le := qLE
  refl := by decide
  antisymm := by decide
  trans := by decide
  rank := Fin.val
  height := 1
  rank_bound := by decide
  minimal_rank := by decide
  maximal_rank := by decide
  cover_rank := by unfold Cover; decide

def productVertices : List (Fin 5 × Fin 2) :=
  (List.finRange 5).flatMap (fun x => (List.finRange 2).map (fun y => (x,y)))
def productLE (x y : Fin 5 × Fin 2) : Bool := P.le x.1 y.1 && Q.le x.2 y.2

def R : RankedPoset (Fin 5 × Fin 2) where
  vertices := productVertices
  nodup := by decide
  complete := by decide
  le := productLE
  refl := by decide
  antisymm := by decide
  trans := by decide
  rank x := P.rank x.1 + Q.rank x.2
  height := P.height + Q.height
  rank_bound := by decide
  minimal_rank := by decide
  maximal_rank := by decide
  cover_rank := by unfold Cover; decide

theorem product_order (x y : Fin 5 × Fin 2) :
    R.le x y = true ↔ P.le x.1 y.1 = true ∧ Q.le x.2 y.2 = true := by
  simp [R, productLE]

theorem product_rank (x : Fin 5 × Fin 2) :
    R.rank x = P.rank x.1 + Q.rank x.2 := rfl

def tuple5 (a b c d e : Bool) (x : Fin 5) : Bool :=
  match x.val with | 0 => a | 1 => b | 2 => c | 3 => d | _ => e

theorem tuple5_eta (f : Fin 5 → Bool) : tuple5 (f 0) (f 1) (f 2) (f 3) (f 4) = f := by
  funext x
  have hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
    have := x.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem checked_P : ∀ a b c d e : Bool,
    Antichain P (tuple5 a b c d e) → lubell P (tuple5 a b c d e) ≤ 1 := by
  unfold Antichain
  decide

theorem P_is_LYM : LYM P := by
  intro f hf
  have h := checked_P (f 0) (f 1) (f 2) (f 3) (f 4)
  rw [tuple5_eta] at h
  exact h hf

def tuple2 (a b : Bool) (x : Fin 2) : Bool := if x = 0 then a else b
theorem tuple2_eta (f : Fin 2 → Bool) : tuple2 (f 0) (f 1) = f := by
  funext x
  have hx : x = 0 ∨ x = 1 := by have := x.isLt; omega
  rcases hx with rfl | rfl <;> rfl

theorem checked_Q : ∀ a b : Bool,
    Antichain Q (tuple2 a b) → lubell Q (tuple2 a b) ≤ 1 := by
  unfold Antichain
  decide

theorem Q_is_LYM : LYM Q := by
  intro f hf
  have h := checked_Q (f 0) (f 1)
  rw [tuple2_eta] at h
  exact h hf

/-- {(a,top),(c,bottom),(d,bottom),(e,bottom)}. -/
def witness (x : Fin 5 × Fin 2) : Bool :=
  decide ((x.1 = 0 ∧ x.2 = 1) ∨ (2 ≤ x.1.val ∧ x.2 = 0))

theorem witness_antichain : Antichain R witness := by unfold Antichain; decide
theorem factor_rank_sizes :
    (List.range 3).map (rankSize P) = [1,1,3] ∧
    (List.range 2).map (rankSize Q) = [1,1] := by decide
theorem product_rank_sizes : (List.range 4).map (rankSize R) = [1,2,4,3] := by decide
theorem witness_lubell : lubell R witness = (5 : Std.Internal.Rat) / 4 := by decide
theorem witness_exceeds_one : ¬lubell R witness ≤ 1 := by decide

theorem product_not_LYM : ¬LYM R := by
  intro h
  exact witness_exceeds_one (h witness witness_antichain)

/-- The decisive necessary instance of the claimed universal product law. -/
theorem conjecture2594_false : ¬(LYM P → LYM Q → LYM R) := by
  intro h
  exact product_not_LYM (h P_is_LYM Q_is_LYM)

#print axioms every_subset_represented
#print axioms P_is_LYM
#print axioms Q_is_LYM
#print axioms product_order
#print axioms product_not_LYM
#print axioms conjecture2594_false
end Conjecture2594
