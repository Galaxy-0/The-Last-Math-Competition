import Std
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Conjecture2618

/-- Finite quantifiers reduce in the kernel; classical logic occurs only in proof terms. -/
instance finiteExists (n : Nat) (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (¬∀ x, ¬P x) (by
    constructor
    · intro h
      obtain ⟨x, hx⟩ := Classical.not_forall.mp h
      exact ⟨x, Classical.byContradiction hx⟩
    · intro h hn
      obtain ⟨x, hx⟩ := h
      exact hn x hx)

instance boolForall (P : Bool → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (P false ∧ P true) Bool.forall_bool.symm

/-- A lattice, with its partial order and both universal properties explicit. -/
structure LatticeData (V : Type) where
  le : V → V → Prop
  join : V → V → V
  meet : V → V → V
  bot : V
  refl : ∀ x, le x x
  antisymm : ∀ x y, le x y → le y x → x = y
  trans : ∀ x y z, le x y → le y z → le x z
  bot_le : ∀ x, le bot x
  le_join_left : ∀ x y, le x (join x y)
  le_join_right : ∀ x y, le y (join x y)
  join_le : ∀ x y z, le x z → le y z → le (join x y) z
  meet_le_left : ∀ x y, le (meet x y) x
  meet_le_right : ∀ x y, le (meet x y) y
  le_meet : ∀ x y z, le z x → le z y → le z (meet x y)

/-- A representation means exactly that w is the least upper bound of S. -/
def JoinRep {V : Type} (D : LatticeData V) (w : V) (S : V → Prop) : Prop :=
  (∀ x, S x → D.le x w) ∧
    ∀ z, (∀ x, S x → D.le x z) → D.le w z
def ProperSubset {V : Type} (T S : V → Prop) : Prop :=
  (∀ x, T x → S x) ∧ ∃ x, S x ∧ ¬T x
def Irredundant {V : Type} (D : LatticeData V) (w : V) (S : V → Prop) : Prop :=
  JoinRep D w S ∧ ∀ T, ProperSubset T S → ¬JoinRep D w T
def Refines {V : Type} (D : LatticeData V) (S T : V → Prop) : Prop :=
  ∀ x, S x → ∃ y, T y ∧ D.le x y
/-- Irredundant and refining all irredundant representations: the standard definition. -/
def CanonicalJoin {V : Type} (D : LatticeData V) (w : V) (S : V → Prop) : Prop :=
  Irredundant D w S ∧ ∀ T, Irredundant D w T → Refines D S T

theorem irredundant_antichain {V : Type} (D : LatticeData V) (w : V)
    (S : V → Prop) (h : Irredundant D w S)
    (x y : V) (hx : S x) (hy : S y) (hxy : D.le x y) : x = y := by
  classical
  by_cases heq : x = y
  · exact heq
  · let T : V → Prop := fun t => S t ∧ t ≠ x
    have hp : ProperSubset T S := by
      constructor
      · intro t ht
        exact ht.1
      · exact ⟨x, hx, fun ht => ht.2 rfl⟩
    have hj : JoinRep D w T := by
      constructor
      · intro t ht
        exact h.1.1 t ht.1
      · intro z hz
        apply h.1.2 z
        intro t ht
        by_cases htx : t = x
        · subst t
          exact D.trans x y z hxy (hz y ⟨hy, Ne.symm heq⟩)
        · exact hz t ⟨ht, htx⟩
    exact False.elim (h.2 T hp hj)

theorem canonical_unique {V : Type} (D : LatticeData V) (w : V)
    (S T : V → Prop) (hS : CanonicalJoin D w S)
    (hT : CanonicalJoin D w T) : S = T := by
  have oneWay : ∀ A B : V → Prop, CanonicalJoin D w A →
      CanonicalJoin D w B → ∀ x, A x → B x := by
    intro A B hA hB x hx
    obtain ⟨y, hy, hxy⟩ := hA.2 B hB.1 x hx
    obtain ⟨z, hz, hyz⟩ := hB.2 A hA.1 y hy
    have hxz : x = z :=
      irredundant_antichain D w A hA.1 x z hx hz (D.trans x y z hxy hyz)
    have hyx : D.le y x := by simpa [← hxz] using hyz
    have hxyEq : x = y := D.antisymm x y hxy hyx
    simpa [hxyEq] using hy
  funext x
  exact propext ⟨oneWay S T hS hT x, oneWay T S hT hS x⟩

abbrev V := Fin 7
/-- Labels: empty, a, b, ab, c, ac, abc. The subset bc is omitted. -/
def mask (x : V) : Nat := if x.val < 6 then x.val else 7
def label (n : Nat) : V :=
  match n with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | _ => 6
def leq (x y : V) : Prop := Nat.land (mask x) (mask y) = mask x
def sup (x y : V) : V := label (Nat.lor (mask x) (mask y))
def inf (x y : V) : V := label (Nat.land (mask x) (mask y))
instance (x y : V) : Decidable (leq x y) := inferInstanceAs (Decidable (_ = _))

def seven : LatticeData V where
  le := leq
  join := sup
  meet := inf
  bot := 0
  refl := by decide
  antisymm := by decide
  trans := by decide
  bot_le := by decide
  le_join_left := by decide
  le_join_right := by decide
  join_le := by decide
  meet_le_left := by decide
  meet_le_right := by decide
  le_meet := by decide

abbrev Code := Fin 128
def decode (c : Code) (v : V) : Prop := (c.val / 2 ^ v.val) % 2 = 1
instance (c : Code) (v : V) : Decidable (decode c v) :=
  inferInstanceAs (Decidable (_ = _))
def tuple7 (b0 b1 b2 b3 b4 b5 b6 : Bool) (v : V) : Bool :=
  match v.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | _ => b6
theorem tuple7_eta (f : V → Bool) :
    tuple7 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) = f := by
  funext v
  have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by
    have bound := v.isLt
    simp only [Fin.ext_iff]
    omega
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Kernel-checked completeness of binary encoding for all Boolean functions. -/
theorem checked_encoding :
    ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      ∃ c : Code, ∀ v : V,
        decide (decode c v) = tuple7 b0 b1 b2 b3 b4 b5 b6 v := by decide

/-- Every actual subset, not only a supplied list, has a code. -/
theorem every_subset_encoded (S : V → Prop) : ∃ c : Code, decode c = S := by
  classical
  let f : V → Bool := fun v => decide (S v)
  obtain ⟨c, hc⟩ := checked_encoding (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
  refine ⟨c, ?_⟩
  funext v
  have hd : decide (decode c v) = decide (S v) := by
    simpa only [tuple7_eta] using hc v
  apply propext
  constructor
  · intro hv
    have ht : decide (S v) = true := by rw [← hd]; exact decide_eq_true hv
    exact of_decide_eq_true ht
  · intro hv
    have ht : decide (decode c v) = true := by rw [hd]; exact decide_eq_true hv
    exact of_decide_eq_true ht

instance (w : V) (c : Code) : Decidable (JoinRep seven w (decode c)) :=
  inferInstanceAs (Decidable ((∀ x, decode c x → leq x w) ∧
    ∀ z, (∀ x, decode c x → leq x z) → leq w z))
instance (b c : Code) : Decidable (ProperSubset (decode b) (decode c)) :=
  inferInstanceAs (Decidable ((∀ x, decode b x → decode c x) ∧
    ∃ x, decode c x ∧ ¬decode b x))
instance (b c : Code) : Decidable (Refines seven (decode b) (decode c)) :=
  inferInstanceAs (Decidable (∀ x, decode b x → ∃ y, decode c y ∧ leq x y))

def IrredCode (w : V) (c : Code) : Prop :=
  JoinRep seven w (decode c) ∧
    ∀ b : Code, ProperSubset (decode b) (decode c) → ¬JoinRep seven w (decode b)
instance (w : V) (c : Code) : Decidable (IrredCode w c) :=
  inferInstanceAs (Decidable (JoinRep seven w (decode c) ∧
    ∀ b : Code, ProperSubset (decode b) (decode c) → ¬JoinRep seven w (decode b)))

theorem irredCode_iff (w : V) (c : Code) :
    IrredCode w c ↔ Irredundant seven w (decode c) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro T ht
    obtain ⟨b, rfl⟩ := every_subset_encoded T
    exact h.2 b ht
  · intro h
    exact ⟨h.1, fun b => h.2 (decode b)⟩

/-- Stronger than needed: the certificate refines every join representation. -/
def Certificate (w : V) (c : Code) : Prop :=
  IrredCode w c ∧ ∀ b : Code,
    JoinRep seven w (decode b) → Refines seven (decode c) (decode b)
instance (w : V) (c : Code) : Decidable (Certificate w c) :=
  inferInstanceAs (Decidable (IrredCode w c ∧ ∀ b : Code,
    JoinRep seven w (decode b) → Refines seven (decode c) (decode b)))
def rep (w : V) : Code :=
  match w.val with
  | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 6 | 4 => 16 | 5 => 18 | _ => 20

theorem checked_certificates : ∀ w : V, Certificate w (rep w) := by decide

theorem all_have_canonical (w : V) : CanonicalJoin seven w (decode (rep w)) := by
  have hc := checked_certificates w
  refine ⟨(irredCode_iff w (rep w)).mp hc.1, ?_⟩
  intro T ht
  obtain ⟨b, rfl⟩ := every_subset_encoded T
  exact hc.2 b ht.1

def AllUniqueCanonical {V : Type} (D : LatticeData V) : Prop :=
  ∀ w, ∃ S, CanonicalJoin D w S ∧ ∀ T, CanonicalJoin D w T → T = S
theorem all_unique_canonical : AllUniqueCanonical seven := by
  intro w
  refine ⟨decode (rep w), all_have_canonical w, ?_⟩
  intro T ht
  exact canonical_unique seven w T (decode (rep w)) ht (all_have_canonical w)

def JoinSemidistributive {V : Type} (D : LatticeData V) : Prop :=
  ∀ x y z, D.join x y = D.join x z →
    D.join x (D.meet y z) = D.join x y
def MeetSemidistributive {V : Type} (D : LatticeData V) : Prop :=
  ∀ x y z, D.meet x y = D.meet x z →
    D.meet x (D.join y z) = D.meet x y
def Semidistributive {V : Type} (D : LatticeData V) : Prop :=
  JoinSemidistributive D ∧ MeetSemidistributive D

theorem join_semidistributive : JoinSemidistributive seven := by
  unfold JoinSemidistributive
  change ∀ x y z : V, sup x y = sup x z → sup x (inf y z) = sup x y
  decide
theorem not_meet_semidistributive : ¬MeetSemidistributive seven := by
  intro h
  have bad := h 1 2 4 (by decide)
  have unequal : seven.meet 1 (seven.join 2 4) ≠ seven.meet 1 2 := by decide
  exact unequal bad
theorem not_semidistributive : ¬Semidistributive seven :=
  fun h => not_meet_semidistributive h.2

/-- The reverse implication claimed in the source, on every labelled finite lattice. -/
def ClaimedCriterion : Prop :=
  ∀ n : Nat, ∀ D : LatticeData (Fin n), AllUniqueCanonical D → Semidistributive D

/-- A finite lattice satisfies the full canonical-join antecedent and fails the conclusion. -/
theorem counterexample :
    AllUniqueCanonical seven ∧ ¬Semidistributive seven :=
  ⟨all_unique_canonical, not_semidistributive⟩
theorem conjecture2618_false : ¬ClaimedCriterion := by
  intro h
  exact not_semidistributive (h 7 seven all_unique_canonical)

#print axioms all_unique_canonical
#print axioms counterexample
#print axioms conjecture2618_false

end Conjecture2618
