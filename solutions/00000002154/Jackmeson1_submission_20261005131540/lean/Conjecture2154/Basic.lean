import Mathlib

/-!
# Conjecture 00000002154 (disproved)

*Statement.* The graphs whose critical group `Jac(G)` has zero cyclic factors (i.e. `Jac(G)` is
trivial) are exactly the subdivisions of closed Eulerian graphs.

*Refutation (direction "subdivision of closed Eulerian ⇒ zero cyclic factors").*  For every
`m ≥ 3` the cycle `C_m` is a closed Eulerian graph (connected, with an Eulerian circuit), hence a
subdivision (with zero subdivided edges) of a closed Eulerian graph, but `Jac(C_m)` maps onto
`ℤ/m`; in particular it is nontrivial, and every decomposition of it as a direct sum has a
nontrivial summand.

`Jac(G)` is the Baker–Norine / Biggs critical group `Div⁰(G) / Prin(G)`, where `Div⁰(G)` is the
group of integer vectors on the vertices with coordinate sum `0` and `Prin(G)` is the image of
the (integer) graph Laplacian `L = D - A` (Mathlib's `SimpleGraph.lapMatrix`).
-/

open SimpleGraph Matrix

namespace C2154

section Defs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Divisors of degree zero: integer vectors on the vertices with coordinate sum `0`. -/
def divZero (V : Type*) [Fintype V] : Submodule ℤ (V → ℤ) where
  carrier := {x | ∑ v, x v = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at *
    rw [hx, mul_zero]

/-- Principal divisors: the image of the integer Laplacian `L = D - A`. -/
def prin (G : SimpleGraph V) [DecidableRel G.Adj] : Submodule ℤ (V → ℤ) :=
  LinearMap.range (Matrix.mulVecLin (G.lapMatrix ℤ))

/-- Principal divisors have degree zero (the column sums of `L` vanish). -/
theorem prin_le_divZero (G : SimpleGraph V) [DecidableRel G.Adj] : prin G ≤ divZero V := by
  rintro _ ⟨f, rfl⟩
  show ∑ v, (G.lapMatrix ℤ *ᵥ f) v = 0
  have h1 : ∑ v, (G.lapMatrix ℤ *ᵥ f) v = (fun _ => (1 : ℤ)) ⬝ᵥ (G.lapMatrix ℤ *ᵥ f) := by
    simp [dotProduct]
  rw [h1, dotProduct_mulVec, ← mulVec_transpose, (isSymm_lapMatrix (R := ℤ) (G := G)).eq,
    lapMatrix_mulVec_const_eq_zero, zero_dotProduct]

/-- The critical group (Jacobian, sandpile group) `Jac(G) = Div⁰(G) / Prin(G)`. -/
abbrev Jac (G : SimpleGraph V) [DecidableRel G.Adj] : Type _ :=
  divZero V ⧸ (prin G).comap (divZero V).subtype

/-- One step of subdivision: the edge `uv` of `H` is replaced by the path `u - new - v`, where
the new vertex is `none : Option W`. -/
def subdivideEdge {W : Type} (H : SimpleGraph W) (u v : W) : SimpleGraph (Option W) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | some x, some y => H.Adj x y ∧ s(x, y) ≠ s(u, v)
    | none, some y => y = u ∨ y = v
    | _, _ => False

/-- `IsSubdivision G H`: `H` is (isomorphic to) a graph obtained from `G` by a finite sequence of
edge subdivisions (possibly none). -/
inductive IsSubdivision : {V : Type} → SimpleGraph V → {W : Type} → SimpleGraph W → Prop
  | refl {V : Type} (G : SimpleGraph V) : IsSubdivision G G
  | step {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} {u v : W} :
      IsSubdivision G H → H.Adj u v → IsSubdivision G (subdivideEdge H u v)
  | iso {V W W' : Type} {G : SimpleGraph V} {H : SimpleGraph W} {H' : SimpleGraph W'} :
      IsSubdivision G H → Nonempty (H ≃g H') → IsSubdivision G H'

/-- A closed Eulerian graph: connected and admitting a closed walk that uses every edge exactly
once (an Eulerian circuit). -/
def IsClosedEulerian {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∃ (v : V) (p : G.Walk v v), p.IsEulerian

/-- `H` is a subdivision of some closed Eulerian graph. -/
def IsSubdivOfClosedEulerian {W : Type} (H : SimpleGraph W) : Prop :=
  ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V), IsClosedEulerian G ∧ IsSubdivision G H

/-- The reduced Laplacian: the integer Laplacian with the row and column of the sink `q`
deleted. -/
def redLap (G : SimpleGraph V) [DecidableRel G.Adj] (q : V) :
    Matrix {v // v ≠ q} {v // v ≠ q} ℤ :=
  (G.lapMatrix ℤ).submatrix Subtype.val Subtype.val

/-- The sandpile group in its other standard form: the cokernel `ℤ^{V∖q} / Δ' ℤ^{V∖q}` of the
reduced Laplacian. -/
abbrev SandpileGroup (G : SimpleGraph V) [DecidableRel G.Adj] (q : V) : Type _ :=
  ({v // v ≠ q} → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin (redLap G q))

end Defs

/-! ### Cycles are closed Eulerian -/

theorem cycleGraph_isClosedEulerian (n : ℕ) : IsClosedEulerian (cycleGraph (n + 3)) := by
  refine ⟨cycleGraph_connected, 0, cycleGraph.cycle n, ?_⟩
  set p := cycleGraph.cycle n
  have ht : p.IsTrail := cycleGraph.isCycle_cycle.isTrail
  refine ht.isEulerian_of_forall_mem ?_
  -- `p` has `n + 3` distinct edges and the cycle graph has `n + 3` edges.
  have hcardE : (cycleGraph (n + 3)).edgeFinset.card = n + 3 := by
    have h := (cycleGraph (n + 3)).sum_degrees_eq_twice_card_edges
    simp only [cycleGraph_degree_three_le, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h
    omega
  have hsub : p.edges.toFinset ⊆ (cycleGraph (n + 3)).edgeFinset := by
    intro e he
    rw [List.mem_toFinset] at he
    rw [mem_edgeFinset]
    exact p.edges_subset_edgeSet he
  have hcardp : p.edges.toFinset.card = n + 3 := by
    rw [List.toFinset_card_of_nodup ht.edges_nodup, Walk.length_edges, cycleGraph.length_cycle]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcardE, hcardp])
  intro e he
  rw [← mem_edgeFinset, ← heq, List.mem_toFinset] at he
  exact he

theorem cycleGraph_isSubdivOfClosedEulerian (n : ℕ) :
    IsSubdivOfClosedEulerian (cycleGraph (n + 3)) :=
  ⟨Fin (n + 3), inferInstance, cycleGraph (n + 3), cycleGraph_isClosedEulerian n, .refl _⟩

/-! ### The critical group of a cycle maps onto `ℤ/m` -/

section Cycle

variable (n : ℕ)

/-- The weight `i ↦ i mod m` on the vertices of `C_m`, `m = n + 3`. -/
def wt (i : Fin (n + 3)) : ZMod (n + 3) := ((i : ℕ) : ZMod (n + 3))

lemma wt_add_one (i : Fin (n + 3)) : wt n (i + 1) = wt n i + 1 := by
  simp only [wt, Fin.val_add, ZMod.natCast_mod, Fin.val_one, Nat.cast_add, Nat.cast_one]

lemma wt_sub_one (i : Fin (n + 3)) : wt n (i - 1) = wt n i - 1 := by
  have := wt_add_one n (i - 1)
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

/-- `φ(x) = ∑ᵢ i · xᵢ (mod m)`. -/
def phi : (Fin (n + 3) → ℤ) →ₗ[ℤ] ZMod (n + 3) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => ∑ i, wt n i * (x i : ZMod (n + 3))
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib] }

lemma phi_apply (x : Fin (n + 3) → ℤ) : phi n x = ∑ i, wt n i * (x i : ZMod (n + 3)) := rfl

/-- The Laplacian of `C_m`: `(L f)ᵢ = 2 fᵢ - f_{i-1} - f_{i+1}`. -/
lemma lap_cycle_apply (f : Fin (n + 3) → ℤ) (i : Fin (n + 3)) :
    ((cycleGraph (n + 3)).lapMatrix ℤ *ᵥ f) i = 2 * f i - f (i - 1) - f (i + 1) := by
  have hne : i - 1 ≠ i + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc i, left_eq_add]
    exact ne_of_beq_false rfl
  rw [lapMatrix_mulVec_apply, cycleGraph_neighborFinset, Finset.sum_pair hne,
    cycleGraph_degree_three_le]
  push_cast; ring

/-- `φ` kills principal divisors of `C_m`. -/
lemma phi_lap (f : Fin (n + 3) → ℤ) : phi n ((cycleGraph (n + 3)).lapMatrix ℤ *ᵥ f) = 0 := by
  rw [phi_apply]
  simp only [lap_cycle_apply, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, mul_sub,
    Finset.sum_sub_distrib]
  have h1 : ∑ i, wt n i * (f (i - 1) : ZMod (n + 3)) = ∑ j, wt n (j + 1) * (f j : ZMod (n + 3)) :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun i => by simp)
  have h2 : ∑ i, wt n i * (f (i + 1) : ZMod (n + 3)) = ∑ j, wt n (j - 1) * (f j : ZMod (n + 3)) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun i => by simp)
  rw [h1, h2]
  simp only [wt_add_one, wt_sub_one, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i _
  ring

/-- The degree-zero divisor `δ₁ - δ₀` on `C_m`. -/
def witness : divZero (Fin (n + 3)) :=
  ⟨(Pi.single (1 : Fin (n + 3)) (1 : ℤ) : Fin (n + 3) → ℤ) - Pi.single (0 : Fin (n + 3)) (1 : ℤ), by
    show ∑ v, ((Pi.single (1 : Fin (n + 3)) (1 : ℤ) : Fin (n + 3) → ℤ) v
      - (Pi.single (0 : Fin (n + 3)) (1 : ℤ) : Fin (n + 3) → ℤ) v) = 0
    simp [Finset.sum_sub_distrib]⟩

lemma phi_witness : phi n (witness n : Fin (n + 3) → ℤ) = 1 := by
  rw [phi_apply]
  simp only [witness, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
  have hs : ∀ k : Fin (n + 3),
      ∑ i, wt n i * (((Pi.single k (1 : ℤ) : Fin (n + 3) → ℤ) i : ℤ) : ZMod (n + 3)) = wt n k := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [hs, hs]
  simp [wt]

/-- The homomorphism `Jac(C_m) → ℤ/m` induced by `φ`. -/
def jacToZMod : Jac (cycleGraph (n + 3)) →ₗ[ℤ] ZMod (n + 3) :=
  Submodule.liftQ _ ((phi n).comp (divZero (Fin (n + 3))).subtype) (by
    rintro x hx
    obtain ⟨f, hf⟩ := (Submodule.mem_comap.mp hx)
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      show (x : Fin (n + 3) → ℤ) = (cycleGraph (n + 3)).lapMatrix ℤ *ᵥ f from hf.symm]
    exact phi_lap n f)

lemma jacToZMod_witness : jacToZMod n (Submodule.Quotient.mk (witness n)) = 1 := by
  rw [jacToZMod, Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    phi_witness]

/-- `Jac(C_m)` surjects onto `ℤ/m`, for every `m = n + 3 ≥ 3`. -/
theorem jacToZMod_surjective : Function.Surjective (jacToZMod n) := by
  intro z
  refine ⟨(z.val : ℤ) • Submodule.Quotient.mk (witness n), ?_⟩
  rw [map_zsmul, jacToZMod_witness, zsmul_one, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- `Jac(C_m)` is nontrivial for every `m ≥ 3`. -/
theorem jac_cycle_nontrivial : Nontrivial (Jac (cycleGraph (n + 3))) := by
  refine ⟨⟨Submodule.Quotient.mk (witness n), 0, fun h => ?_⟩⟩
  have h1 := congrArg (jacToZMod n) h
  rw [jacToZMod_witness, map_zero] at h1
  have : Fact (1 < n + 3) := ⟨by omega⟩
  exact one_ne_zero h1

/-- Every direct-sum decomposition of `Jac(C_m)` has at least one nontrivial summand; in
particular `Jac(C_m)` does not have zero (nontrivial) cyclic factors. -/
theorem jac_cycle_has_cyclic_factor (k : ℕ) (C : Fin k → Type) [∀ i, AddCommGroup (C i)]
    (e : Jac (cycleGraph (n + 3)) ≃+ DirectSum (Fin k) C) : ∃ i, Nontrivial (C i) := by
  by_contra h
  push Not at h
  have hD : Subsingleton (DirectSum (Fin k) C) :=
    ⟨fun a b => DFinsupp.ext fun i => (h i).elim _ _⟩
  have hJ : Subsingleton (Jac (cycleGraph (n + 3))) := e.injective.subsingleton
  have := jac_cycle_nontrivial n
  exact not_subsingleton _ hJ

/-! #### The same for the reduced-Laplacian cokernel (sink `0`) -/

lemma sum_ne_zero_eq {R : Type*} [AddCommMonoid R] (g : Fin (n + 3) → R) (hg : g 0 = 0) :
    ∑ i : {v : Fin (n + 3) // v ≠ 0}, g i = ∑ v, g v := by
  rw [← Finset.sum_subtype (Finset.univ.erase 0) (fun x => by simp), Finset.sum_erase _ hg]

/-- Extension by `0` at the sink. -/
def extZ (f : {v : Fin (n + 3) // v ≠ 0} → ℤ) : Fin (n + 3) → ℤ :=
  fun v => if h : v = 0 then 0 else f ⟨v, h⟩

lemma redLap_mulVec (f : {v : Fin (n + 3) // v ≠ 0} → ℤ) (i : {v : Fin (n + 3) // v ≠ 0}) :
    (redLap (cycleGraph (n + 3)) 0 *ᵥ f) i =
      ((cycleGraph (n + 3)).lapMatrix ℤ *ᵥ extZ n f) i := by
  simp only [redLap, mulVec, dotProduct, submatrix_apply]
  rw [← sum_ne_zero_eq n (fun v => (cycleGraph (n + 3)).lapMatrix ℤ i v * extZ n f v)
    (by simp [extZ])]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [extZ, j.2]

/-- `φ'(y) = ∑_{i ≠ 0} i · yᵢ (mod m)`. -/
def phiRed : ({v : Fin (n + 3) // v ≠ 0} → ℤ) →ₗ[ℤ] ZMod (n + 3) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun y => ∑ i : {v : Fin (n + 3) // v ≠ 0}, wt n i * (y i : ZMod (n + 3))
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib] }

lemma phiRed_lap (f : {v : Fin (n + 3) // v ≠ 0} → ℤ) :
    phiRed n (redLap (cycleGraph (n + 3)) 0 *ᵥ f) = 0 := by
  have h := phi_lap n (extZ n f)
  rw [phi_apply, ← sum_ne_zero_eq n _ (by simp [wt])] at h
  rw [← h]
  show ∑ i : {v : Fin (n + 3) // v ≠ 0},
    wt n i * (((redLap (cycleGraph (n + 3)) 0 *ᵥ f) i : ℤ) : ZMod (n + 3)) = _
  simp only [redLap_mulVec]

/-- The homomorphism `ℤ^{V∖0} / Δ' ℤ^{V∖0} → ℤ/m` induced by `φ'`. -/
def sandpileToZMod : SandpileGroup (cycleGraph (n + 3)) 0 →ₗ[ℤ] ZMod (n + 3) :=
  Submodule.liftQ _ (phiRed n) (by
    rintro _ ⟨f, rfl⟩
    exact phiRed_lap n f)

lemma one_ne_zero' : (1 : Fin (n + 3)) ≠ 0 := by
  rw [Ne, Fin.ext_iff]; simp

/-- The reduced-Laplacian cokernel of `C_m` also surjects onto `ℤ/m`. -/
theorem sandpileToZMod_surjective : Function.Surjective (sandpileToZMod n) := by
  have hw : sandpileToZMod n (Submodule.Quotient.mk (Pi.single ⟨1, one_ne_zero' n⟩ 1)) = 1 := by
    rw [sandpileToZMod, Submodule.liftQ_apply]
    show ∑ i : {v : Fin (n + 3) // v ≠ 0}, wt n i * ((Pi.single
      (⟨1, one_ne_zero' n⟩ : {v : Fin (n + 3) // v ≠ 0}) (1 : ℤ)
      : {v : Fin (n + 3) // v ≠ 0} → ℤ) i : ZMod (n + 3)) = 1
    rw [Finset.sum_eq_single ⟨1, one_ne_zero' n⟩]
    · simp [wt]
    · intro b _ hb; simp [hb]
    · simp
  intro z
  refine ⟨(z.val : ℤ) • Submodule.Quotient.mk (Pi.single ⟨1, one_ne_zero' n⟩ 1), ?_⟩
  rw [map_zsmul, hw, zsmul_one, Int.cast_natCast, ZMod.natCast_zmod_val]

end Cycle

/-- **Main theorem.**  For every `m = n + 3 ≥ 3`, the cycle `C_m` is a subdivision of a closed
Eulerian graph (namely of itself), yet its critical group is nontrivial: both standard models,
`Div⁰/Prin` and the reduced-Laplacian cokernel, map onto `ℤ/m`.
Hence "subdivision of a closed Eulerian graph ⇒ `Jac(G)` has zero cyclic factors" fails for the
infinite family of all cycles, and the claimed classification is false. -/
theorem not_classification :
    ∀ n : ℕ, IsSubdivOfClosedEulerian (cycleGraph (n + 3)) ∧
      Nontrivial (Jac (cycleGraph (n + 3))) ∧
      (∃ π : Jac (cycleGraph (n + 3)) →ₗ[ℤ] ZMod (n + 3), Function.Surjective π) ∧
      ∃ π : SandpileGroup (cycleGraph (n + 3)) 0 →ₗ[ℤ] ZMod (n + 3), Function.Surjective π :=
  fun n => ⟨cycleGraph_isSubdivOfClosedEulerian n, jac_cycle_nontrivial n,
    ⟨jacToZMod n, jacToZMod_surjective n⟩, sandpileToZMod n, sandpileToZMod_surjective n⟩

/-- The classification, as stated, is false: not every subdivision of a closed Eulerian graph has
trivial critical group. -/
theorem not_conjecture :
    ¬ ∀ m : ℕ, IsSubdivOfClosedEulerian (cycleGraph m) → Subsingleton (Jac (cycleGraph m)) := by
  intro h
  have := h 3 (cycleGraph_isSubdivOfClosedEulerian 0)
  exact (jac_cycle_nontrivial 0).exists_pair_ne.elim fun a ha =>
    ha.elim fun b hab => hab (Subsingleton.elim a b)

end C2154
