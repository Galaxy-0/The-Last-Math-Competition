import Std

namespace Conjecture261

def sq (n : Nat) : Nat := n*n

/- For nonnegative integer coefficients, this is the exact comparison
   t+u*sqrt(d) <= s+v*sqrt(d), obtained by squaring nonnegative sides.
   The common positive denominator 2 does not affect the comparison. -/
def ValueLE (d t u s v : Nat) : Prop :=
  if u ≤ v then t ≤ s ∨ sq (t-s) ≤ d*sq (v-u)
  else t ≤ s ∧ d*sq (u-v) ≤ sq (s-t)

theorem value_le_of_coefficients (d t u s v : Nat) (ht : t ≤ s) (hu : u ≤ v) :
    ValueLE d t u s v := by
  simp [ValueLE, hu, ht]

theorem square_zero (n : Nat) (h : sq n ≤ 0) : n = 0 := by
  by_cases hn : n=0
  · exact hn
  · have hp : 0 < n*n := Nat.mul_pos (by omega) (by omega)
    simp only [sq] at h
    omega

theorem value_equality_at_coordinate_minimum (d t u s v : Nat)
    (hd : 0 < d) (ht : s ≤ t) (hu : v ≤ u) (h : ValueLE d t u s v) :
    t=s ∧ u=v := by
  by_cases huv : u ≤ v
  · have huvEq : u=v := by omega
    subst u
    simp only [ValueLE, Nat.le_refl, if_true, Nat.sub_self, sq,
      Nat.mul_zero] at h
    rcases h with h | h
    · exact ⟨by omega,rfl⟩
    · have hz := square_zero (t-s) h
      exact ⟨by omega,rfl⟩
  · simp only [ValueLE, huv, if_false] at h
    have hts : t=s := by omega
    subst t
    have bound : sq (u-v) ≤ d*sq (u-v) := by
      have hh := Nat.mul_le_mul_right (sq (u-v)) (show 1 ≤ d by omega)
      simpa using hh
    have hz : sq (u-v) ≤ 0 := by
      have hh := h.2
      simp only [Nat.sub_self] at hh
      change d*sq (u-v) ≤ 0 at hh
      omega
    have heq := square_zero (u-v) hz
    exact ⟨rfl,by omega⟩

def Squarefree (d : Nat) : Prop := ∀ a, sq a ∣ d → a=1
def FundamentalDiscriminantOneModFour (d : Nat) : Prop :=
  1 < d ∧ d%4=1 ∧ Squarefree d

theorem five_fundamental_discriminant : FundamentalDiscriminantOneModFour 5 := by
  refine ⟨by decide,by decide,?_⟩
  intro a ha
  have hb : sq a ≤ 5 := Nat.le_of_dvd (by decide) ha
  have hal : a < 3 := by
    by_cases h : a < 3
    · exact h
    · have hh : 9 ≤ a*a := Nat.mul_le_mul (show 3 ≤ a by omega) (show 3 ≤ a by omega)
      simp only [sq] at hb
      omega
  have finite : ∀ x : Fin 3, sq x.val ∣ 5 → x.val=1 := by decide
  exact finite ⟨a,hal⟩ ha

def PellUnit (d t u : Nat) : Prop :=
  0 < t ∧ 0 < u ∧ t%2=u%2 ∧ (sq t = d*sq u+4 ∨ sq t+4 = d*sq u)

def PositiveNormPell (d t u : Nat) : Prop :=
  0 < t ∧ 0 < u ∧ t%2=u%2 ∧ sq t = d*sq u+4

def FundamentalUnitPell (d t u : Nat) : Prop :=
  PellUnit d t u ∧ ∀ s v, PellUnit d s v → ValueLE d t u s v

def FundamentalPositivePell (d t u : Nat) : Prop :=
  PositiveNormPell d t u ∧ ∀ s v, PositiveNormPell d s v → ValueLE d t u s v

theorem unit_witness : PellUnit 5 1 1 := by
  unfold PellUnit sq
  decide
theorem positive_norm_witness : PositiveNormPell 5 3 1 := by
  unfold PositiveNormPell sq
  decide

theorem positive_norm_coefficient_bound (t u : Nat) (h : PositiveNormPell 5 t u) :
    3 ≤ t ∧ 1 ≤ u := by
  have hu : 1 ≤ u := by exact h.2.1
  have hu2 : 1 ≤ sq u := Nat.mul_le_mul hu hu
  have htEq := h.2.2.2
  have hlt : 3 ≤ t := by
    by_cases hl : 3 ≤ t
    · exact hl
    · have alternatives : t=0 ∨ t=1 ∨ t=2 := by omega
      rcases alternatives with ht | ht | ht <;> subst t <;> simp only [sq] at htEq hu2 <;> omega
  exact ⟨hlt,hu⟩

theorem fundamental_unit_five : FundamentalUnitPell 5 1 1 := by
  refine ⟨unit_witness,?_⟩
  intro t u h
  exact value_le_of_coefficients 5 1 1 t u h.1 h.2.1

theorem fundamental_positive_five : FundamentalPositivePell 5 3 1 := by
  refine ⟨positive_norm_witness,?_⟩
  intro t u h
  have bounds := positive_norm_coefficient_bound t u h
  exact value_le_of_coefficients 5 3 1 t u bounds.1 bounds.2

theorem fundamental_unit_five_unique (t u : Nat) (h : FundamentalUnitPell 5 t u) :
    t=1 ∧ u=1 := by
  exact value_equality_at_coordinate_minimum 5 t u 1 1 (by decide)
    h.1.1 h.1.2.1 (h.2 1 1 unit_witness)

theorem fundamental_positive_five_unique (t u : Nat) (h : FundamentalPositivePell 5 t u) :
    t=3 ∧ u=1 := by
  have bounds := positive_norm_coefficient_bound t u h.1
  exact value_equality_at_coordinate_minimum 5 t u 3 1 (by decide)
    bounds.1 bounds.2 (h.2 3 1 positive_norm_witness)

theorem literal_counterexample :
    FundamentalDiscriminantOneModFour 5 ∧ FundamentalUnitPell 5 1 1 ∧ (1:Nat) ∣ 1 :=
  ⟨five_fundamental_discriminant,fundamental_unit_five,by decide⟩

theorem positive_norm_counterexample :
    FundamentalDiscriminantOneModFour 5 ∧ FundamentalPositivePell 5 3 1 ∧ (1:Nat) ∣ 3 :=
  ⟨five_fundamental_discriminant,fundamental_positive_five,by decide⟩

theorem conjecture261_false :
    ¬ (∀ d t u, FundamentalDiscriminantOneModFour d → FundamentalUnitPell d t u → ¬u∣t) := by
  intro h
  exact h 5 1 1 literal_counterexample.1 literal_counterexample.2.1 literal_counterexample.2.2

theorem conjecture261_positive_norm_false :
    ¬ (∀ d t u, FundamentalDiscriminantOneModFour d → FundamentalPositivePell d t u → ¬u∣t) := by
  intro h
  exact h 5 3 1 positive_norm_counterexample.1 positive_norm_counterexample.2.1 positive_norm_counterexample.2.2

#print axioms five_fundamental_discriminant
#print axioms fundamental_unit_five
#print axioms fundamental_positive_five
#print axioms fundamental_unit_five_unique
#print axioms fundamental_positive_five_unique
#print axioms conjecture261_false
#print axioms conjecture261_positive_norm_false
end Conjecture261
