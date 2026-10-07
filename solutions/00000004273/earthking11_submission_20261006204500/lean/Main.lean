import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
The group C₂ × C₄ and its actual Ulm quotient groups.  The cardinal-valued
invariant is the cardinality of Uₙ/Uₙ₊₁, where Uₙ=(2ⁿG)[2].
-/
namespace TLMC4273

abbrev G := ZMod 2 × ZMod 4

instance decidableExistsG (P : G → Prop) [DecidablePred P] : Decidable (∃ x, P x) :=
  Fintype.decidableExistsFintype

def doubleHom : G →+ G where
  toFun x := (2 • x.1, 2 • x.2)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

def iterDouble : Nat → G →+ G
  | 0 => AddMonoidHom.id G
  | n + 1 => (iterDouble n).comp doubleHom

theorem doubleHom_eq_two_smul (x : G) : doubleHom x = 2 • x := rfl

theorem iterDouble_eq_power_smul (n : Nat) (x : G) : iterDouble n x = (2 ^ n) • x := by
  induction n generalizing x with
  | zero => simp [iterDouble]
  | succ n ih =>
      change iterDouble n (doubleHom x) = (2 ^ (n + 1)) • x
      rw [ih, doubleHom_eq_two_smul, pow_succ, mul_smul]

def powerImage (n : Nat) : AddSubgroup G := (iterDouble n).range
def twoTorsion : AddSubgroup G := doubleHom.ker
def UlmLayer (n : Nat) : AddSubgroup G := powerImage n ⊓ twoTorsion

instance (n : Nat) : DecidablePred (fun x : G => x ∈ powerImage n) := by
  intro x
  letI : DecidablePred (fun y : G => iterDouble n y = x) := fun _ => inferInstance
  exact decidable_of_iff (∃ y : G, iterDouble n y = x)
    AddMonoidHom.mem_range.symm

instance (n : Nat) : DecidablePred (fun x : G => x ∈ UlmLayer n) := by
  intro x
  change Decidable ((x ∈ powerImage n) ∧ doubleHom x = 0)
  infer_instance

theorem powerImage_succ_le (n : Nat) : powerImage (n+1) ≤ powerImage n := by
  intro x hx
  rcases (AddMonoidHom.mem_range).mp hx with ⟨y, rfl⟩
  exact (AddMonoidHom.mem_range).mpr ⟨doubleHom y, rfl⟩

theorem ulmLayer_succ_le (n : Nat) : UlmLayer (n+1) ≤ UlmLayer n := by
  exact inf_le_inf (powerImage_succ_le n) le_rfl

abbrev LayerType (n : Nat) := {x : G // x ∈ UlmLayer n}

def nextLayerIn (n : Nat) : AddSubgroup (LayerType n) :=
  (UlmLayer (n+1)).comap
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

abbrev UlmQuotient (n : Nat) := LayerType n ⧸ nextLayerIn n

noncomputable def ulmInvariant (n : Nat) : Nat := Nat.card (UlmQuotient n)
noncomputable def UlmSequence : Nat → Nat := ulmInvariant

def NatStrictAnti (s : Nat → Nat) : Prop := ∀ n, s (n+1) < s n

def IsTwoPrimary (A : Type) [AddCommGroup A] : Prop :=
  ∀ x : A, ∃ n : Nat, (2 ^ n) • x = 0

theorem group_is_countable : Countable G := inferInstance

theorem group_is_two_primary : IsTwoPrimary G := by
  intro x
  refine ⟨2, ?_⟩
  rcases x with ⟨a, b⟩
  norm_num [pow_succ]
  change (4 * a = 0) ∧ (4 * b = 0)
  have ha : (4 : ZMod 2) = 0 := by
    calc
      (4 : ZMod 2) = (2 : ZMod 2) * 2 := by norm_num
      _ = 0 := by
        rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2]
        simp
  have hb : (4 : ZMod 4) = 0 := ZMod.natCast_self 4
  rw [ha, hb]
  simp

theorem ulmLayer_zero_description (x : G) :
    x ∈ UlmLayer 0 ↔ x.2 = 0 ∨ x.2 = 2 := by
  rcases x with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

theorem ulmLayer_one_description (x : G) :
    x ∈ UlmLayer 1 ↔ x.1 = 0 ∧ (x.2 = 0 ∨ x.2 = 2) := by
  rcases x with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

theorem ulmLayer_two_description (x : G) :
    x ∈ UlmLayer 2 ↔ x = 0 := by
  rcases x with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

theorem zmod4_zero_ne_two : (0 : ZMod 4) ≠ 2 := by decide
theorem zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

def coordinate0 : LayerType 0 →+ ZMod 2 where
  toFun x := x.1.1
  map_zero' := rfl
  map_add' _ _ := rfl

def coordinate1 : LayerType 1 →+ ZMod 2 where
  toFun x := if x.1.2 = 2 then 1 else 0
  map_zero' := by simp [zmod4_zero_ne_two]
  map_add' a b := by
    obtain ⟨x, hx⟩ := a
    obtain ⟨y, hy⟩ := b
    have hx' := (ulmLayer_one_description x).mp hx
    have hy' := (ulmLayer_one_description y).mp hy
    rcases hx' with ⟨_, hx₂⟩
    rcases hy' with ⟨_, hy₂⟩
    change (if x.2 + y.2 = 2 then (1 : ZMod 2) else 0) =
      (if x.2 = 2 then 1 else 0) + (if y.2 = 2 then 1 else 0)
    rcases hx₂ with hx₂ | hx₂ <;> rcases hy₂ with hy₂ | hy₂
    all_goals rw [hx₂, hy₂]
    all_goals decide

theorem coordinate0_surjective : Function.Surjective coordinate0 := by
  intro t
  fin_cases t
  · refine ⟨⟨(0, 0), ?_⟩, ?_⟩
    · exact (ulmLayer_zero_description _).2 (Or.inl rfl)
    · rfl
  · refine ⟨⟨(1, 0), ?_⟩, ?_⟩
    · exact (ulmLayer_zero_description _).2 (Or.inl rfl)
    · rfl

theorem coordinate1_surjective : Function.Surjective coordinate1 := by
  intro t
  fin_cases t
  · refine ⟨⟨(0, 0), ?_⟩, ?_⟩
    · exact (ulmLayer_one_description _).2 ⟨rfl, Or.inl rfl⟩
    · rfl
  · refine ⟨⟨(0, 2), ?_⟩, ?_⟩
    · exact (ulmLayer_one_description _).2 ⟨rfl, Or.inr rfl⟩
    · rfl

theorem nextLayer0_eq_coordinate0_ker : nextLayerIn 0 = coordinate0.ker := by
  ext x
  change x.1 ∈ UlmLayer 1 ↔ coordinate0 x = 0
  constructor
  · intro hx
    simpa [coordinate0] using (ulmLayer_one_description x.1).mp hx |>.1
  · intro hx
    apply (ulmLayer_one_description x.1).2
    refine ⟨?_, (ulmLayer_zero_description x.1).mp x.2⟩
    simpa [coordinate0] using hx

theorem nextLayer1_eq_coordinate1_ker : nextLayerIn 1 = coordinate1.ker := by
  ext x
  change x.1 ∈ UlmLayer 2 ↔ coordinate1 x = 0
  have hx := (ulmLayer_one_description x.1).mp x.2
  rcases hx with ⟨hx₁, hx₂⟩
  constructor
  · intro h
    have hxzero : x = 0 := Subtype.ext ((ulmLayer_two_description x.1).mp h)
    rw [hxzero]
    simp [coordinate1, zmod4_zero_ne_two]
  · intro h
    rcases hx₂ with hzero | htwo
    · apply (ulmLayer_two_description x.1).2
      exact Prod.ext hx₁ hzero
    · simp [coordinate1, htwo] at h

theorem quotient0_card : Nat.card (UlmQuotient 0) = 2 := by
  have heq : nextLayerIn 0 = coordinate0.ker := nextLayer0_eq_coordinate0_ker
  let e₁ : UlmQuotient 0 ≃ LayerType 0 ⧸ coordinate0.ker :=
    AddSubgroup.quotientEquivOfEq heq
  let e₂ : LayerType 0 ⧸ coordinate0.ker ≃+ ZMod 2 :=
    QuotientAddGroup.quotientKerEquivOfSurjective coordinate0 coordinate0_surjective
  rw [Nat.card_congr (e₁.trans e₂.toEquiv)]
  exact Nat.card_zmod 2

theorem quotient1_card : Nat.card (UlmQuotient 1) = 2 := by
  have heq : nextLayerIn 1 = coordinate1.ker := nextLayer1_eq_coordinate1_ker
  let e₁ : UlmQuotient 1 ≃ LayerType 1 ⧸ coordinate1.ker :=
    AddSubgroup.quotientEquivOfEq heq
  let e₂ : LayerType 1 ⧸ coordinate1.ker ≃+ ZMod 2 :=
    QuotientAddGroup.quotientKerEquivOfSurjective coordinate1 coordinate1_surjective
  rw [Nat.card_congr (e₁.trans e₂.toEquiv)]
  exact Nat.card_zmod 2

noncomputable def quotient0Equiv : UlmQuotient 0 ≃ ZMod 2 :=
  (AddSubgroup.quotientEquivOfEq nextLayer0_eq_coordinate0_ker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective coordinate0 coordinate0_surjective).toEquiv

noncomputable def quotient1Equiv : UlmQuotient 1 ≃ ZMod 2 :=
  (AddSubgroup.quotientEquivOfEq nextLayer1_eq_coordinate1_ker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective coordinate1 coordinate1_surjective).toEquiv

noncomputable def CardinalSequence : Nat → Cardinal := fun n => Cardinal.mk (UlmQuotient n)

theorem cardinalSequence_zero_eq_one : CardinalSequence 0 = CardinalSequence 1 := by
  unfold CardinalSequence
  exact Cardinal.mk_congr (quotient0Equiv.trans quotient1Equiv.symm)

theorem cardinalStrictAnti_fails : ¬ _root_.StrictAnti CardinalSequence := by
  intro h
  have h01 : CardinalSequence 1 < CardinalSequence 0 :=
    h (show (0 : Nat) < 1 by decide)
  rw [cardinalSequence_zero_eq_one] at h01
  exact lt_irrefl _ h01

theorem ulmInvariant_zero_eq_two : ulmInvariant 0 = 2 := quotient0_card
theorem ulmInvariant_one_eq_two : ulmInvariant 1 = 2 := quotient1_card

theorem adjacent_ulm_quotient_cardinalities_equal :
    UlmSequence 1 = UlmSequence 0 := by
  rw [UlmSequence, ulmInvariant_zero_eq_two, ulmInvariant_one_eq_two]

theorem natStrictAnti_fails : ¬ NatStrictAnti UlmSequence := by
  intro h
  have h01 : UlmSequence 1 < UlmSequence 0 := h 0
  rw [adjacent_ulm_quotient_cardinalities_equal] at h01
  exact Nat.lt_irrefl _ h01

theorem counterexample_fails_strict_cardinal_decrease :
    Countable G ∧ IsTwoPrimary G ∧ ¬ _root_.StrictAnti CardinalSequence :=
  ⟨group_is_countable, group_is_two_primary, cardinalStrictAnti_fails⟩

#print axioms quotient0_card
#print axioms quotient1_card
#print axioms cardinalStrictAnti_fails
#print axioms counterexample_fails_strict_cardinal_decrease

end TLMC4273
