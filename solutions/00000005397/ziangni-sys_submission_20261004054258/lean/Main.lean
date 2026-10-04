import Mathlib.Topology.Instances.AddCircle
import Mathlib.Data.Real.Irrational
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.NormNum

namespace TorusTranslation
noncomputable section

abbrev Circle := AddCircle (1 : ℝ)
abbrev Torus := Circle × Circle

def frequency (i : Fin 2) : ℝ := if i = 0 then Real.sqrt 2 else 1

theorem independent_components : LinearIndependent ℚ frequency := by
  rw [linearIndependent_fin2]
  constructor
  · norm_num [frequency]
  · intro a h
    have heq : (a : ℝ) = Real.sqrt 2 := by
      simpa [frequency, Rat.smul_def] using h
    exact irrational_sqrt_two ⟨a, heq⟩

def theta : Torus := ((Real.sqrt 2 : ℝ), (1 : ℝ))
def translation (x : Torus) : Torus := x + theta
def inverseTranslation (x : Torus) : Torus := x - theta
def integerOrbit (x : Torus) (n : ℤ) : Torus := x + n • theta

theorem theta_from_frequency :
    theta = ((frequency 0 : Circle), (frequency 1 : Circle)) := by
  simp [theta, frequency]

theorem translation_continuous : Continuous translation :=
  continuous_id.add continuous_const

theorem inverse_identities (x : Torus) :
    inverseTranslation (translation x) = x ∧
    translation (inverseTranslation x) = x := by
  simp [inverseTranslation, translation]

theorem theta_second : theta.2 = 0 := AddCircle.coe_period (1 : ℝ)

theorem orbit_step (x : Torus) (n : ℤ) :
    integerOrbit x (n + 1) = translation (integerOrbit x n) := by
  simp [integerOrbit, translation, add_zsmul, add_assoc]

theorem orbit_inverse_step (x : Torus) (n : ℤ) :
    integerOrbit x (n - 1) = inverseTranslation (integerOrbit x n) := by
  simp [integerOrbit, inverseTranslation, sub_eq_add_neg, add_zsmul, add_assoc]

theorem iterate_eq (x : Torus) (n : ℕ) :
    translation^[n] x = integerOrbit x (n : ℤ) := by
  induction n with
  | zero => simp [integerOrbit]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simpa only [Nat.cast_add, Nat.cast_one] using (orbit_step x (n : ℤ)).symm

theorem all_integer_orbits_in_fiber (x : Torus) (n : ℤ) :
    (integerOrbit x n).2 = x.2 := by
  simp [integerOrbit, theta_second]

def fiber (x : Torus) : Set Torus := {y | y.2 = x.2}

theorem fiber_closed (x : Torus) : IsClosed (fiber x) :=
  isClosed_eq continuous_snd continuous_const

def half : Circle := ((1 / 2 : ℝ) : Circle)

theorem half_nonzero : half ≠ 0 := by
  have hmem : (1 / 2 : ℝ) ∈ Set.Ico 0 1 := by norm_num
  intro h
  have hz := (AddCircle.coe_eq_zero_iff_of_mem_Ico hmem).mp h
  norm_num at hz

theorem fiber_proper (x : Torus) : ∃ y, y ∉ fiber x := by
  refine ⟨(x.1, x.2 + half), ?_⟩
  intro h
  have heq : x.2 + half = x.2 + 0 := by simpa [fiber] using h
  exact half_nonzero (add_left_cancel heq)

theorem integer_orbit_not_dense (x : Torus) :
    ¬ Dense (Set.range (integerOrbit x)) := by
  intro hdense
  have hsubset : Set.range (integerOrbit x) ⊆ fiber x := by
    rintro y ⟨n, rfl⟩
    exact all_integer_orbits_in_fiber x n
  have hclosure := (fiber_closed x).closure_subset_iff.mpr hsubset
  obtain ⟨y, hy⟩ := fiber_proper x
  exact hy (hclosure (hdense y))

theorem forward_orbit_not_dense (x : Torus) :
    ¬ Dense (Set.range (fun n : ℕ => translation^[n] x)) := by
  intro hdense
  apply integer_orbit_not_dense x
  exact hdense.mono (by
    rintro y ⟨n, rfl⟩
    exact ⟨(n : ℤ), (iterate_eq x n).symm⟩)

theorem counterexample :
    LinearIndependent ℚ frequency ∧
    Continuous translation ∧
    (∀ x, ¬ Dense (Set.range (integerOrbit x))) ∧
    (∀ x, ¬ Dense (Set.range (fun n : ℕ => translation^[n] x))) :=
  ⟨independent_components, translation_continuous,
    integer_orbit_not_dense, forward_orbit_not_dense⟩

#print axioms independent_components
#print axioms iterate_eq
#print axioms fiber_closed
#print axioms fiber_proper
#print axioms integer_orbit_not_dense
#print axioms counterexample

end
end TorusTranslation
