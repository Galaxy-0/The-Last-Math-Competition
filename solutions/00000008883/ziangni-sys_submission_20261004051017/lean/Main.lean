import Mathlib.Data.Real.Cardinality
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.DeriveCountable

noncomputable section
namespace FiniteHackenbush8883

-- Edge identities are distinct even when their endpoints coincide: multigraphs.
structure Graph (V E : Type*) where
  source : E → V
  target : E → V
  blue : E → Bool
  ground : V → Bool

structure Description (v e : ℕ) where
  source : Fin e → Fin v
  target : Fin e → Fin v
  blue : Fin e → Bool
  ground : Fin v → Bool
  deriving Countable

def Description.toGraph {v e : ℕ} (D : Description v e) : Graph (Fin v) (Fin e) :=
  ⟨D.source, D.target, D.blue, D.ground⟩
abbrev FiniteDescription := Σ v : ℕ, Σ e : ℕ, Description v e

def IsRelabelling {V E W F : Type*} (G : Graph V E) (H : Graph W F)
    (p : V ≃ W) (q : E ≃ F) : Prop :=
  (∀ i, H.source (q i) = p (G.source i)) ∧
  (∀ i, H.target (q i) = p (G.target i)) ∧
  (∀ i, H.blue (q i) = G.blue i) ∧
  (∀ x, H.ground (p x) = G.ground x)

def describe {V E : Type*} [Fintype V] [Fintype E] (G : Graph V E) :
    Description (Fintype.card V) (Fintype.card E) where
  source i := Fintype.equivFin V (G.source ((Fintype.equivFin E).symm i))
  target i := Fintype.equivFin V (G.target ((Fintype.equivFin E).symm i))
  blue i := G.blue ((Fintype.equivFin E).symm i)
  ground x := G.ground ((Fintype.equivFin V).symm x)

theorem describe_preserves_everything {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) : IsRelabelling G (describe G).toGraph
      (Fintype.equivFin V) (Fintype.equivFin E) := by
  constructor
  · intro i; simp [describe, Description.toGraph]
  constructor
  · intro i; simp [describe, Description.toGraph]
  constructor
  · intro i; simp [describe, Description.toGraph]
  · intro x; simp [describe, Description.toGraph]

-- An arbitrary vertex type is permitted. Finite edges have finite endpoint support.
def support {V E : Type*} [Fintype E] (G : Graph V E) : Finset V := by
  classical
  exact Finset.univ.image G.source ∪ Finset.univ.image G.target

theorem source_in_support {V E : Type*} [Fintype E] (G : Graph V E) (i : E) :
    G.source i ∈ support G := by
  classical
  simp only [support, Finset.mem_union, Finset.mem_image]
  exact Or.inl ⟨i, Finset.mem_univ _, rfl⟩

theorem target_in_support {V E : Type*} [Fintype E] (G : Graph V E) (i : E) :
    G.target i ∈ support G := by
  classical
  simp only [support, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨i, Finset.mem_univ _, rfl⟩

abbrev IncidentVertex {V E : Type*} [Fintype E] (G : Graph V E) :=
  {x : V // x ∈ support G}

def normalize {V E : Type*} [Fintype E] (G : Graph V E) : Graph (IncidentVertex G) E where
  source i := ⟨G.source i, source_in_support G i⟩
  target i := ⟨G.target i, target_in_support G i⟩
  blue := G.blue
  ground x := G.ground x.val

theorem normalization_preserves_incidence {V E : Type*} [Fintype E] (G : Graph V E) :
    (∀ i, ((normalize G).source i).val = G.source i) ∧
    (∀ i, ((normalize G).target i).val = G.target i) ∧
    (∀ i, (normalize G).blue i = G.blue i) ∧
    (∀ x, (normalize G).ground x = G.ground x.val) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem exhaustive_finite_edge_representation {V E : Type*} [Fintype E]
    (G : Graph V E) : ∃ (v e : ℕ) (D : Description v e)
      (p : IncidentVertex G ≃ Fin v) (q : E ≃ Fin e),
      IsRelabelling (normalize G) D.toGraph p q := by
  classical
  letI : Fintype (IncidentVertex G) := (support G).fintypeCoeSort
  exact ⟨_, _, describe (normalize G), Fintype.equivFin _, Fintype.equivFin _,
    describe_preserves_everything (normalize G)⟩

instance descriptions_countable : Countable FiniteDescription := inferInstance

theorem no_value_assignment_realizes_all_reals (value : FiniteDescription → ℝ) :
    ¬ Function.Surjective value :=
  not_surjective_countable_uncountable value

theorem omitted_real (value : FiniteDescription → ℝ) : ∃ r : ℝ, ∀ D, value D ≠ r := by
  have h := no_value_assignment_realizes_all_reals value
  simpa only [Function.Surjective, not_forall, not_exists] using h

theorem no_partial_value_assignment (eligible : FiniteDescription → Prop)
    (value : {D // eligible D} → ℝ) : ¬ Function.Surjective value :=
  not_surjective_countable_uncountable value

-- Also covers positions without real values: only uniqueness is needed.
theorem no_functional_realization_covers_all_reals
    (Realizes : FiniteDescription → ℝ → Prop)
    (unique : ∀ D r s, Realizes D r → Realizes D s → r = s) :
    ¬ ∀ r : ℝ, ∃ D, Realizes D r := by
  classical
  intro hall
  let eligible := fun D => ∃ r, Realizes D r
  let value : {D // eligible D} → ℝ := fun D => D.property.choose
  have hs : Function.Surjective value := by
    intro r
    obtain ⟨D, hD⟩ := hall r
    let d : {D // eligible D} := ⟨D, ⟨r, hD⟩⟩
    exact ⟨d, unique D (value d) r d.property.choose_spec hD⟩
  exact no_partial_value_assignment eligible value hs

end FiniteHackenbush8883
#print axioms FiniteHackenbush8883.exhaustive_finite_edge_representation
#print axioms FiniteHackenbush8883.no_value_assignment_realizes_all_reals
#print axioms FiniteHackenbush8883.omitted_real
#print axioms FiniteHackenbush8883.no_functional_realization_covers_all_reals
