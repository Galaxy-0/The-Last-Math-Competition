import Mathlib

/-!
# Conjecture 00000002450: a nondiscrete Polish group all of whose Borel actions are smooth

Statement: there exists a Polish group `G` all of whose Borel-action orbit equivalence relations
are smooth, while `G` is nondiscrete.

We prove that every compact Polish group has this property (all its Borel actions on standard
Borel spaces have smooth orbit equivalence relations), and that the Cantor group
`Multiplicative (ℕ → ZMod 2)` is a compact, nondiscrete Polish group.
-/

open MeasureTheory Set

namespace C2450

/-- An equivalence relation `E` on a measurable space `X` is *smooth* if there are a Polish space
`Y` and a Borel map `f : X → Y` with `E x y ↔ f x = f y` for all `x y`. -/
def IsSmooth {X : Type*} [MeasurableSpace X] (E : X → X → Prop) : Prop :=
  ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : PolishSpace Y) (_ : MeasurableSpace Y)
    (_ : BorelSpace Y) (f : X → Y), Measurable f ∧ ∀ x y, E x y ↔ f x = f y

/-- The orbit equivalence relation of an action: `x ~ y` iff `g • x = y` for some `g`. -/
def orbitEquivRel (G X : Type*) [Group G] [MulAction G X] (x y : X) : Prop :=
  ∃ g : G, g • x = y

/-- `G` is *all-smooth*: for every standard Borel space `X` and every Borel action of `G` on `X`
(a group action whose action map `G × X → X` is Borel), the orbit equivalence relation is
smooth. -/
def AllSmooth.{u} (G : Type) [Group G] [MeasurableSpace G] : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] [StandardBorelSpace X] [MulAction G X],
    Measurable (fun p : G × X => p.1 • p.2) → IsSmooth (orbitEquivRel G X)

section Compact

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Every compact Polish group is all-smooth. The complete invariant is
`x ↦ (μ {g | e (g⁻¹ • x) < q})_{q ∈ ℚ}`, where `μ` is a Haar measure on `G` and `e` is a Borel
embedding of `X` into `ℝ`. -/
theorem allSmooth_of_compact : AllSmooth.{u} G := by
  intro X _ _ _ hact
  set μ : Measure G := Measure.haar
  set e : X → ℝ := embeddingReal X
  have he : MeasurableEmbedding e := measurableEmbedding_embeddingReal X
  have hmx : ∀ x : X, Measurable fun g : G => g • x := fun x =>
    hact.comp (measurable_id.prodMk measurable_const)
  have hm : ∀ x : X, Measurable fun g : G => e (g⁻¹ • x) := fun x =>
    he.measurable.comp (hact.comp (measurable_inv.prodMk measurable_const))
  -- the invariant
  let f : X → (ℚ → ℝ) := fun x q => (μ ((fun g : G => e (g⁻¹ • x)) ⁻¹' Iio (q : ℝ))).toReal
  -- invariance under the action
  have hinv : ∀ (h : G) (x : X), f (h • x) = f x := by
    intro h x
    funext q
    have : (fun g : G => e (g⁻¹ • (h • x))) ⁻¹' Iio (q : ℝ) =
        (fun g : G => h⁻¹ * g) ⁻¹' ((fun g : G => e (g⁻¹ • x)) ⁻¹' Iio (q : ℝ)) := by
      ext g; simp [mul_smul]
    simp only [f, this, measure_preimage_mul]
  refine ⟨ℚ → ℝ, inferInstance, inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩
  · -- Borel measurability (Fubini)
    refine measurable_pi_lambda _ fun q => ?_
    have hS : MeasurableSet {p : X × G | e (p.2⁻¹ • p.1) < (q : ℝ)} :=
      measurableSet_Iio.preimage
        (he.measurable.comp (hact.comp (measurable_snd.inv.prodMk measurable_fst)))
    exact (measurable_measure_prodMk_left (ν := μ) hS).ennreal_toReal
  intro x y
  constructor
  · rintro ⟨h, rfl⟩
    exact (hinv h x).symm
  intro hxy
  by_contra hne
  -- the two orbits are disjoint
  have hdisj : Disjoint (range fun g : G => g • x) (range fun g : G => g • y) := by
    rw [Set.disjoint_left]
    rintro _ ⟨g, rfl⟩ ⟨k, hk⟩
    simp only at hk
    exact hne ⟨k⁻¹ * g, by rw [mul_smul, ← hk, inv_smul_smul]⟩
  -- Lusin separation for a compatible Polish topology on `X`
  obtain ⟨τ, hB, hP⟩ := (‹StandardBorelSpace X›).polish
  let := τ
  have := hB
  have := hP
  have hAx : AnalyticSet (range fun g : G => g • x) := by
    rw [← image_univ]; exact MeasurableSet.univ.analyticSet_image (hmx x)
  have hAy : AnalyticSet (range fun g : G => g • y) := by
    rw [← image_univ]; exact MeasurableSet.univ.analyticSet_image (hmx y)
  obtain ⟨A, hxA, hyA, hAm⟩ := hAx.measurablySeparable hAy hdisj
  -- the pushforward measures on `ℝ` agree
  have hmeas : μ.map (fun g : G => e (g⁻¹ • x)) = μ.map (fun g : G => e (g⁻¹ • y)) := by
    refine ext_of_generate_finite (⋃ a : ℚ, {Iio (a : ℝ)}) ?_ Real.isPiSystem_Iio_rat ?_ ?_
    · exact Real.borel_eq_generateFrom_Iio_rat
    · intro s hs
      simp only [mem_iUnion, mem_singleton_iff] at hs
      obtain ⟨q, rfl⟩ := hs
      rw [Measure.map_apply (hm x) measurableSet_Iio, Measure.map_apply (hm y) measurableSet_Iio]
      have := congrFun hxy q
      simp only [f] at this
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this
    · rw [Measure.map_apply (hm x) MeasurableSet.univ, Measure.map_apply (hm y) MeasurableSet.univ]
      rfl
  have hEA : MeasurableSet (e '' A) := he.measurableSet_image.2 hAm
  have h1 : μ.map (fun g : G => e (g⁻¹ • x)) (e '' A) = μ univ := by
    rw [Measure.map_apply (hm x) hEA]
    congr 1
    ext g
    simp only [mem_preimage, mem_univ, iff_true]
    exact ⟨g⁻¹ • x, hxA ⟨g⁻¹, rfl⟩, rfl⟩
  have h2 : μ.map (fun g : G => e (g⁻¹ • y)) (e '' A) = 0 := by
    rw [Measure.map_apply (hm y) hEA]
    convert measure_empty (μ := μ)
    ext g
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    rintro ⟨a, ha, hea⟩
    have : a = g⁻¹ • y := he.injective hea
    exact Set.disjoint_left.1 hyA ⟨g⁻¹, this.symm⟩ ha
  have hpos : μ univ ≠ 0 := (isOpen_univ.measure_pos μ univ_nonempty).ne'
  rw [hmeas, h2] at h1
  exact hpos h1.symm

end Compact

/-- The Cantor group `(ℤ/2ℤ)^ℕ`, written multiplicatively. -/
abbrev Cantor := Multiplicative (ℕ → ZMod 2)

instance : SecondCountableTopology (ZMod 2) := DiscreteTopology.secondCountableTopology_of_countable

instance : PolishSpace Cantor := inferInstanceAs (PolishSpace (ℕ → ZMod 2))

instance : MeasurableSpace Cantor := inferInstanceAs (MeasurableSpace (ℕ → ZMod 2))

instance : BorelSpace Cantor := inferInstanceAs (BorelSpace (ℕ → ZMod 2))

/-- The Cantor group is not discrete: it is compact and infinite. -/
theorem cantor_not_discrete : ¬ DiscreteTopology Cantor := by
  intro h
  have : Finite Cantor := finite_of_compact_of_discrete
  have : Infinite Cantor := inferInstanceAs (Infinite (ℕ → ZMod 2))
  exact _root_.not_finite Cantor

/-- **Main theorem.** There exists a nondiscrete Polish group all of whose Borel-action orbit
equivalence relations (on standard Borel spaces in universe `u`) are smooth. -/
theorem exists_nondiscrete_allSmooth_polishGroup :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (_ : PolishSpace G) (_ : MeasurableSpace G) (_ : BorelSpace G),
      ¬ DiscreteTopology G ∧ AllSmooth.{u} G :=
  ⟨Cantor, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, cantor_not_discrete, allSmooth_of_compact Cantor⟩

end C2450
