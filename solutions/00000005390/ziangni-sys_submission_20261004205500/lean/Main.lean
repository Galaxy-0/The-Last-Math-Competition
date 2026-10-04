import Mathlib.Logic.Function.Iterate
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Logic.Equiv.Set

namespace ConjugateCycles
universe u
variable {X Y : Type u} (f : X → X) (g : Y → Y) (e : X ≃ Y)

def Conjugacy : Prop := ∀ x, e (f x) = g (e x)
def Periodic (f : X → X) (n : ℕ) (x : X) : Prop := f^[n] x = x
def ExactPeriod (f : X → X) (n : ℕ) (x : X) : Prop :=
  0 < n ∧ Periodic f n x ∧ ∀ k, 0 < k → k < n → ¬ Periodic f k x

theorem intertwines_iterates (h : Conjugacy f g e) (n : ℕ) (x : X) :
    e (f^[n] x) = g^[n] (e x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [h, ih]

theorem periodic_iff (h : Conjugacy f g e) (n : ℕ) (x : X) :
    Periodic f n x ↔ Periodic g n (e x) := by
  unfold Periodic
  rw [← intertwines_iterates f g e h]
  exact e.injective.eq_iff.symm

theorem exact_period_iff (h : Conjugacy f g e) (n : ℕ) (x : X) :
    ExactPeriod f n x ↔ ExactPeriod g n (e x) := by
  simp only [ExactPeriod, periodic_iff f g e h]

def periodicEquiv (h : Conjugacy f g e) (n : ℕ) :
    {x // Periodic f n x} ≃ {y // Periodic g n y} where
  toFun := fun x => ⟨e x.val, (periodic_iff f g e h n x.val).1 x.property⟩
  invFun := fun y => ⟨e.symm y.val, by
    apply (periodic_iff f g e h n (e.symm y.val)).2
    simpa using y.property⟩
  left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
  right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val)

def exactPeriodEquiv (h : Conjugacy f g e) (n : ℕ) :
    {x // ExactPeriod f n x} ≃ {y // ExactPeriod g n y} where
  toFun := fun x => ⟨e x.val, (exact_period_iff f g e h n x.val).1 x.property⟩
  invFun := fun y => ⟨e.symm y.val, by
    apply (exact_period_iff f g e h n (e.symm y.val)).2
    simpa using y.property⟩
  left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
  right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val)

theorem periodic_cardinal_eq (h : Conjugacy f g e) (n : ℕ) :
    Cardinal.mk {x // Periodic f n x} = Cardinal.mk {y // Periodic g n y} :=
  Cardinal.mk_congr (periodicEquiv f g e h n)

theorem exact_period_cardinal_eq (h : Conjugacy f g e) (n : ℕ) :
    Cardinal.mk {x // ExactPeriod f n x} = Cardinal.mk {y // ExactPeriod g n y} :=
  Cardinal.mk_congr (exactPeriodEquiv f g e h n)

theorem finite_periodic_count_eq (h : Conjugacy f g e) (n : ℕ)
    [Fintype {x // Periodic f n x}] [Fintype {y // Periodic g n y}] :
    Fintype.card {x // Periodic f n x} = Fintype.card {y // Periodic g n y} :=
  Fintype.card_congr (periodicEquiv f g e h n)

theorem finite_exact_period_count_eq (h : Conjugacy f g e) (n : ℕ)
    [Fintype {x // ExactPeriod f n x}] [Fintype {y // ExactPeriod g n y}] :
    Fintype.card {x // ExactPeriod f n x} = Fintype.card {y // ExactPeriod g n y} :=
  Fintype.card_congr (exactPeriodEquiv f g e h n)

theorem exact_period_separation_impossible :
    ¬ ∃ e : X ≃ Y, Conjugacy f g e ∧
      ∃ n, Cardinal.mk {x // ExactPeriod f n x} ≠ Cardinal.mk {y // ExactPeriod g n y} := by
  rintro ⟨e, h, n, hn⟩
  exact hn (exact_period_cardinal_eq f g e h n)

theorem conjecture_5390_conjugate_separation_impossible :
    ¬ ∃ e : X ≃ Y, Conjugacy f g e ∧
      ∃ n, Cardinal.mk {x // Periodic f n x} ≠ Cardinal.mk {y // Periodic g n y} := by
  rintro ⟨e, h, n, hn⟩
  exact hn (periodic_cardinal_eq f g e h n)

def Orbit (f : X → X) (x : X) : Set X := Set.range (fun k : ℕ => f^[k] x)
def Cycles (f : X → X) (n : ℕ) : Set (Set X) :=
  {S | ∃ x, ExactPeriod f n x ∧ S = Orbit f x}

theorem reachability_iff (h : Conjugacy f g e) (k : ℕ) (x y : X) :
    f^[k] x = y ↔ g^[k] (e x) = e y := by
  rw [← intertwines_iterates f g e h]
  exact e.injective.eq_iff.symm

theorem orbit_image (h : Conjugacy f g e) (x : X) :
    e '' Orbit f x = Orbit g (e x) := by
  ext y
  constructor
  · rintro ⟨z,⟨k,rfl⟩,rfl⟩
    exact ⟨k,(intertwines_iterates f g e h k x).symm⟩
  · rintro ⟨k,rfl⟩
    exact ⟨f^[k] x,⟨k,rfl⟩,intertwines_iterates f g e h k x⟩

theorem inverse_conjugacy (h : Conjugacy f g e) : Conjugacy g f e.symm := by
  intro y
  apply e.injective
  simpa using (h (e.symm y)).symm

theorem image_is_cycle (h : Conjugacy f g e) (n : ℕ) (S : Set X)
    (hS : S ∈ Cycles f n) : e '' S ∈ Cycles g n := by
  obtain ⟨x,hx,rfl⟩ := hS
  exact ⟨e x,(exact_period_iff f g e h n x).mp hx,orbit_image f g e h x⟩

def cycleEquiv (h : Conjugacy f g e) (n : ℕ) :
    {S // S ∈ Cycles f n} ≃ {T // T ∈ Cycles g n} where
  toFun S := ⟨e '' S.val,image_is_cycle f g e h n S.val S.property⟩
  invFun T := ⟨e.symm '' T.val,
    image_is_cycle g f e.symm (inverse_conjugacy f g e h) n T.val T.property⟩
  left_inv S := by
    apply Subtype.ext
    change e.symm '' (e '' S.val) = S.val
    rw [Set.image_image]
    simp
  right_inv T := by
    apply Subtype.ext
    change e '' (e.symm '' T.val) = T.val
    rw [Set.image_image]
    simp

theorem cycle_cardinal_eq (h : Conjugacy f g e) (n : ℕ) :
    Cardinal.mk {S // S ∈ Cycles f n} = Cardinal.mk {T // T ∈ Cycles g n} :=
  Cardinal.mk_congr (cycleEquiv f g e h n)
theorem finite_cycle_count_eq (h : Conjugacy f g e) (n : ℕ)
    [Fintype {S // S ∈ Cycles f n}] [Fintype {T // T ∈ Cycles g n}] :
    Fintype.card {S // S ∈ Cycles f n} = Fintype.card {T // T ∈ Cycles g n} :=
  Fintype.card_congr (cycleEquiv f g e h n)

-- Any additional restrictions (including heights) cannot defeat this universal obstruction.
theorem separation_impossible_with_any_extra_property (P : (X ≃ Y) → Prop) :
    ¬ ∃ e : X ≃ Y, Conjugacy f g e ∧ P e ∧ ∃ n,
      (Cardinal.mk {x // Periodic f n x} ≠ Cardinal.mk {y // Periodic g n y}) ∨
      (Cardinal.mk {x // ExactPeriod f n x} ≠ Cardinal.mk {y // ExactPeriod g n y}) ∨
      (Cardinal.mk {S // S ∈ Cycles f n} ≠ Cardinal.mk {T // T ∈ Cycles g n}) := by
  rintro ⟨e,h,_,n,hd⟩
  rcases hd with hd|hd|hd
  · exact hd (periodic_cardinal_eq f g e h n)
  · exact hd (exact_period_cardinal_eq f g e h n)
  · exact hd (cycle_cardinal_eq f g e h n)

end ConjugateCycles
#print axioms ConjugateCycles.intertwines_iterates
#print axioms ConjugateCycles.periodic_iff
#print axioms ConjugateCycles.exact_period_iff
#print axioms ConjugateCycles.periodicEquiv
#print axioms ConjugateCycles.exactPeriodEquiv
#print axioms ConjugateCycles.reachability_iff
#print axioms ConjugateCycles.orbit_image
#print axioms ConjugateCycles.cycleEquiv
#print axioms ConjugateCycles.cycle_cardinal_eq
#print axioms ConjugateCycles.finite_cycle_count_eq
#print axioms ConjugateCycles.separation_impossible_with_any_extra_property
