import Mathlib

/-!
# Conjecture 00000009629: the orbit-equivalence dimension criterion fails

The conjecture's first clause says: two mixing SFTs are orbit equivalent (orbit-preserving Borel
isomorphism) iff their dimension groups are order-isomorphic. We refute the "if" direction.

* SFTs are edge shifts `X_A` of square matrices `A` over `ℕ` (alphabet: the edges `(i, j, k)`,
  `k < A i j`; a sequence is allowed iff `i(e_{k+1}) = t(e_k)`), built as Mathlib `Subshift`s.
* The dimension group of `A` is `G_A = {x ∈ R(A) | x A^k ∈ ℤ^r for some k ≥ 0}` with positive cone
  `G_A^+ = {x ∈ R(A) | x A^k ∈ ℤ_{≥0}^r for some k ≥ 0}`, where `R(A) = ℚ^r A^r` is the eventual
  range (row vectors).
* Witnesses: the full 2-shift `X_[2]` and the full 4-shift `X_[4]`. Both are topologically
  mixing SFTs; `(G_[2], G_[2]^+) = (G_[4], G_[4]^+)` as subsets of `ℚ^1` (both are `ℤ[1/2]`
  with its usual cone), but no bijection mapping orbits into orbits exists, since it would have
  to send the 4 fixed points of `X_[4]` injectively to the 2 fixed points of `X_[2]`.
-/

open SymbolicDynamics.FullShift Set Matrix

namespace C9629

/-! ## Edge shifts -/

/-- The edges of the graph of a square matrix `A` over `ℕ`: the edges from `i` to `j` are the
triples `(i, j, k)` with `k < A i j`. -/
def Edge {r : ℕ} (A : Matrix (Fin r) (Fin r) ℕ) : Type :=
  Σ p : Fin r × Fin r, Fin (A p.1 p.2)

namespace Edge
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℕ}
instance : Fintype (Edge A) := by unfold Edge; infer_instance
instance : DecidableEq (Edge A) := by unfold Edge; infer_instance
instance : TopologicalSpace (Edge A) := ⊥
instance : DiscreteTopology (Edge A) := ⟨rfl⟩
/-- Initial vertex `i(e)`. -/
def src (e : Edge A) : Fin r := e.1.1
/-- Terminal vertex `t(e)`. -/
def tgt (e : Edge A) : Fin r := e.1.2
end Edge

/-- The edge shift `X_A`: all bi-infinite edge sequences with `i(e_{k+1}) = t(e_k)` for all `k`,
as a Mathlib `Subshift` (closed and shift-invariant). -/
def edgeShift {r : ℕ} (A : Matrix (Fin r) (Fin r) ℕ) : Subshift (Edge A) ℤ where
  carrier := {x | ∀ k : ℤ, (x (k + 1)).src = (x k).tgt}
  isClosed := by
    have h : {x : ℤ → Edge A | ∀ k : ℤ, (x (k + 1)).src = (x k).tgt} =
        ⋂ k : ℤ, (fun x : ℤ → Edge A => (x (k + 1), x k)) ⁻¹' {p | p.1.src = p.2.tgt} := by
      ext x; simp
    rw [h]
    exact isClosed_iInter fun k => (isClosed_discrete _).preimage (by fun_prop)
  mapsTo := by
    intro g x hx k
    have := hx (g + k)
    simp only [shift_apply]
    rwa [← add_assoc]

/-- A subshift of finite type in the sense of Mathlib's forbidden patterns. -/
def IsSFT {α : Type*} [TopologicalSpace α] [Inhabited α] (X : Subshift α ℤ) : Prop :=
  ∃ F : Set (Pattern α ℤ), F.Finite ∧ X.carrier = forbidden F

/-! ## The shift map, mixing, orbits, orbit equivalence -/

section Dyn
variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- The shift map `σ = shift 1` (`(σ x) i = x (i + 1)`) restricted to a subshift. -/
def sigma (X : Subshift α ℤ) : X.carrier → X.carrier :=
  fun x => ⟨shift 1 x.1, X.mapsTo 1 x.2⟩

lemma iterate_sigma (X : Subshift α ℤ) (x : X.carrier) (n : ℕ) (i : ℤ) :
    ((sigma X)^[n] x).1 i = x.1 (n + i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', sigma]
    simp only [shift_apply]
    rw [ih, show (n : ℤ) + (1 + i) = ((n + 1 : ℕ) : ℤ) + i by push_cast; ring]

/-- Topological mixing of `(X, σ)`: for all nonempty open `U, V ⊆ X` there is `N` such that
`σ^n(U) ∩ V ≠ ∅` for every `n > N` (open sets of the subspace topology of `X`). -/
def IsMixing (X : Subshift α ℤ) : Prop :=
  ∀ U V : Set X.carrier, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ((sigma X)^[n] '' U ∩ V).Nonempty

/-- The orbit of `x ∈ X` under the shift action `k ↦ shift k` of `ℤ`. -/
def orbit (X : Subshift α ℤ) (x : X.carrier) : Set X.carrier :=
  {y | ∃ k : ℤ, y.1 = shift k x.1}

/-- Orbit equivalence: an orbit-preserving Borel isomorphism `φ : X → Y` (a bijection, Borel
measurable in both directions for the Borel σ-algebras of the subspace topologies, mapping the
orbit of every `x` onto the orbit of `φ x`). -/
def OrbitEquivalent (X : Subshift α ℤ) (Y : Subshift β ℤ) : Prop :=
  ∃ φ : X.carrier ≃ Y.carrier,
    @Measurable _ _ (borel X.carrier) (borel Y.carrier) φ ∧
    @Measurable _ _ (borel Y.carrier) (borel X.carrier) φ.symm ∧
    ∀ x : X.carrier, φ '' orbit X x = orbit Y (φ x)

omit [TopologicalSpace β] in
/-- A shift-fixed configuration is constant. -/
lemma const_of_fixed {y : ℤ → β} (h : shift 1 y = y) (i : ℤ) : y i = y 0 := by
  have h1 : ∀ i, y (1 + i) = y i := fun i => congrFun h i
  induction i using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [add_comm, h1, ih]
  | pred k ih =>
    rw [← h1]
    have : (1 : ℤ) + (-(k : ℤ) - 1) = -(k : ℤ) := by ring
    rw [this, ih]

omit [TopologicalSpace β] in
lemma shift_fixed {y : ℤ → β} (h : shift 1 y = y) (k : ℤ) : shift k y = y := by
  funext i
  simp only [shift_apply]
  rw [const_of_fixed h, const_of_fixed h i]

/-- If a bijection maps every orbit into an orbit, its inverse sends fixed points to fixed
points. -/
lemma symm_fixed {X : Subshift α ℤ} {Y : Subshift β ℤ} (φ : X.carrier ≃ Y.carrier)
    (hφ : ∀ x, φ '' orbit X x ⊆ orbit Y (φ x)) (y : Y.carrier) (hy : shift 1 y.1 = y.1) :
    shift 1 (φ.symm y).1 = (φ.symm y).1 := by
  have hz : sigma X (φ.symm y) ∈ orbit X (φ.symm y) := ⟨1, rfl⟩
  obtain ⟨k, hk⟩ := hφ _ (mem_image_of_mem φ hz)
  rw [φ.apply_symm_apply, shift_fixed hy k] at hk
  have h2 : φ (sigma X (φ.symm y)) = φ (φ.symm y) := by
    rw [φ.apply_symm_apply]; exact Subtype.ext hk
  exact congrArg Subtype.val (φ.injective h2)

/-- A subshift containing every configuration is topologically mixing. -/
theorem isMixing_of_eq_univ [DiscreteTopology α] (X : Subshift α ℤ) (hX : X.carrier = univ) :
    IsMixing X := by
  intro U V hU hV ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨U', hU'o, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨V', hV'o, rfl⟩ := isOpen_induced_iff.mp hV
  obtain ⟨I, w, hw, hIU⟩ := isOpen_pi_iff.mp hU'o u.1 hu
  obtain ⟨J, w', hw', hJV⟩ := isOpen_pi_iff.mp hV'o v.1 hv
  set M : ℕ := ∑ i ∈ I ∪ J, i.natAbs with hM
  have hbd : ∀ i ∈ I ∪ J, |i| ≤ (M : ℤ) := by
    intro i hi
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Finset.single_le_sum (f := fun i : ℤ => i.natAbs)
      (fun _ _ => Nat.zero_le _) hi
  refine ⟨2 * M, fun n hn => ?_⟩
  classical
  let x : ℤ → α := fun i => if i ∈ I then u.1 i else v.1 (i - n)
  have hxX : x ∈ X.carrier := hX ▸ mem_univ x
  refine ⟨(sigma X)^[n] ⟨x, hxX⟩, ⟨⟨x, hxX⟩, ?_, rfl⟩, ?_⟩
  · show x ∈ U'
    apply hIU
    intro i hi
    simp only [x, if_pos (Finset.mem_coe.mp hi)]
    exact (hw i hi).2
  · show ((sigma X)^[n] ⟨x, hxX⟩).1 ∈ V'
    apply hJV
    intro j hj
    have hj' := Finset.mem_coe.mp hj
    rw [iterate_sigma]
    have hnot : (n : ℤ) + j ∉ I := by
      intro hI
      have h1 := hbd _ (Finset.mem_union_left J hI)
      have h2 := hbd _ (Finset.mem_union_right I hj')
      rw [abs_le] at h1 h2
      omega
    simp only [x, if_neg hnot, add_sub_cancel_left]
    exact (hw' j hj).2

end Dyn

/-! ## Dimension groups -/

section DimGroup
variable {r : ℕ}

/-- `A` viewed as a matrix over `ℚ`. -/
def toQ (A : Matrix (Fin r) (Fin r) ℕ) : Matrix (Fin r) (Fin r) ℚ := A.map (Nat.cast)

/-- The eventual range `R(A) = ℚ^r A^r` (row vectors). -/
def eventualRange (A : Matrix (Fin r) (Fin r) ℕ) : Set (Fin r → ℚ) :=
  Set.range fun w : Fin r → ℚ => w ᵥ* toQ A ^ r

/-- `v ∈ ℤ^r`. -/
def IsIntVec (v : Fin r → ℚ) : Prop := ∀ i, ∃ m : ℤ, v i = m

/-- `v ∈ (ℤ_{≥0})^r`. -/
def IsNatVec (v : Fin r → ℚ) : Prop := ∀ i, ∃ m : ℕ, v i = m

lemma isIntVec_mul (A : Matrix (Fin r) (Fin r) ℕ) {v : Fin r → ℚ} (hv : IsIntVec v) :
    IsIntVec (v ᵥ* toQ A) := by
  choose m hm using hv
  intro i
  refine ⟨∑ j, m j * (A j i : ℤ), ?_⟩
  simp [Matrix.vecMul, dotProduct, toQ, hm]

lemma isIntVec_pow (A : Matrix (Fin r) (Fin r) ℕ) {v : Fin r → ℚ} (hv : IsIntVec v) (k : ℕ) :
    IsIntVec (v ᵥ* toQ A ^ k) := by
  induction k with
  | zero => simpa using hv
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul]; exact isIntVec_mul A ih

/-- The dimension group `G_A = {x ∈ R(A) | x A^k ∈ ℤ^r for some k ≥ 0}`. -/
def dimGroup (A : Matrix (Fin r) (Fin r) ℕ) : AddSubgroup (Fin r → ℚ) where
  carrier := {x | x ∈ eventualRange A ∧ ∃ k : ℕ, IsIntVec (x ᵥ* toQ A ^ k)}
  zero_mem' := ⟨⟨0, by simp⟩, 0, fun _ => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro x y ⟨⟨w, hw⟩, k, hk⟩ ⟨⟨w', hw'⟩, l, hl⟩
    refine ⟨⟨w + w', ?_⟩, k + l, ?_⟩
    · simp only at hw hw' ⊢
      rw [Matrix.add_vecMul, hw, hw']
    have e1 := isIntVec_pow A hk l
    have e2 := isIntVec_pow A hl k
    rw [Matrix.vecMul_vecMul, ← pow_add] at e1 e2
    rw [add_comm l k] at e2
    rw [Matrix.add_vecMul]
    intro i
    obtain ⟨a, ha⟩ := e1 i
    obtain ⟨b, hb⟩ := e2 i
    exact ⟨a + b, by rw [Pi.add_apply, ha, hb]; push_cast; ring⟩
  neg_mem' := by
    rintro x ⟨⟨w, hw⟩, k, hk⟩
    refine ⟨⟨-w, ?_⟩, k, ?_⟩
    · simp only at hw ⊢
      rw [Matrix.neg_vecMul, hw]
    rw [Matrix.neg_vecMul]
    intro i
    obtain ⟨a, ha⟩ := hk i
    exact ⟨-a, by rw [Pi.neg_apply, ha]; push_cast; ring⟩

/-- The positive cone `G_A^+ = {x ∈ R(A) | x A^k ∈ (ℤ_{≥0})^r for some k ≥ 0}`. -/
def dimCone (A : Matrix (Fin r) (Fin r) ℕ) : Set (Fin r → ℚ) :=
  {x | x ∈ eventualRange A ∧ ∃ k : ℕ, IsNatVec (x ᵥ* toQ A ^ k)}

/-- The ordered groups `(G_A, G_A^+)` and `(G_B, G_B^+)` are order-isomorphic: a group
isomorphism carrying the positive cone exactly onto the positive cone. -/
def DimOrderIso {s : ℕ} (A : Matrix (Fin r) (Fin r) ℕ) (B : Matrix (Fin s) (Fin s) ℕ) : Prop :=
  ∃ e : dimGroup A ≃+ dimGroup B,
    ∀ x : dimGroup A, (x : Fin r → ℚ) ∈ dimCone A ↔ (e x : Fin s → ℚ) ∈ dimCone B

end DimGroup

/-! ## The full `n`-shift `X_[n]` -/

/-- The `1 × 1` matrix `[n]`; its edge shift is the full `n`-shift. -/
def full (n : ℕ) : Matrix (Fin 1) (Fin 1) ℕ := !![n]

lemma card_edge_full (n : ℕ) : Fintype.card (Edge (full n)) = n := by
  rw [show Fintype.card (Edge (full n)) =
      Fintype.card (Σ p : Fin 1 × Fin 1, Fin (full n p.1 p.2)) from rfl, Fintype.card_sigma]
  simp [full]

lemma carrier_full (n : ℕ) : (edgeShift (full n)).carrier = univ :=
  eq_univ_of_forall fun _ _ => Subsingleton.elim _ _

instance (n : ℕ) : Inhabited (Edge (full (n + 1))) := ⟨⟨(0, 0), ⟨0, by simp [full]⟩⟩⟩

theorem isSFT_full (n : ℕ) : IsSFT (edgeShift (full (n + 1))) :=
  ⟨∅, finite_empty, by rw [carrier_full]; ext x; simp [forbidden]⟩

theorem isMixing_full (n : ℕ) : IsMixing (edgeShift (full n)) :=
  isMixing_of_eq_univ _ (carrier_full n)

/-- No bijection `X_[m] → X_[n]` with `m < n` maps every orbit into an orbit. -/
theorem no_orbit_map {m n : ℕ} (hmn : m < n) (φ : (edgeShift (full m)).carrier ≃
    (edgeShift (full n)).carrier) : ¬ ∀ x, φ '' orbit _ x ⊆ orbit _ (φ x) := by
  intro hφ
  let c : Edge (full n) → (edgeShift (full n)).carrier :=
    fun e => ⟨fun _ => e, by rw [carrier_full]; trivial⟩
  have hc : ∀ e, shift 1 (c e).1 = (c e).1 := fun _ => rfl
  let f : Edge (full n) → Edge (full m) := fun e => (φ.symm (c e)).1 0
  have hf : Function.Injective f := by
    intro e e' h
    have h1 := symm_fixed φ hφ (c e) (hc e)
    have h2 := symm_fixed φ hφ (c e') (hc e')
    have h3 : φ.symm (c e) = φ.symm (c e') := Subtype.ext (funext fun i => by
      rw [const_of_fixed h1 i, const_of_fixed h2 i]; exact h)
    have h4 := congrArg (fun z : (edgeShift (full n)).carrier => z.1 0) (φ.symm.injective h3)
    simpa [c] using h4
  have := Fintype.card_le_of_injective f hf
  rw [card_edge_full, card_edge_full] at this
  omega

theorem not_orbitEquivalent_full {m n : ℕ} (hmn : m < n) :
    ¬ OrbitEquivalent (edgeShift (full m)) (edgeShift (full n)) := by
  rintro ⟨φ, -, -, hφ⟩
  exact no_orbit_map hmn φ fun x => (hφ x).subset

lemma pow_full (n k : ℕ) : (toQ (full n) ^ k) 0 0 = (n : ℚ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih]
    simp [toQ, full, pow_succ]

lemma vecMul_full (n k : ℕ) (x : Fin 1 → ℚ) (i : Fin 1) :
    (x ᵥ* toQ (full n) ^ k) i = x 0 * (n : ℚ) ^ k := by
  rw [Subsingleton.elim i 0]
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_one]
  rw [pow_full]

lemma eventualRange_full {n : ℕ} (hn : n ≠ 0) : eventualRange (full n) = univ := by
  refine eq_univ_of_forall fun x => ⟨fun _ => x 0 / n, funext fun i => ?_⟩
  beta_reduce
  rw [vecMul_full, Subsingleton.elim i 0]
  field_simp

/-- `G_[n] = {x | x · n^k ∈ ℤ for some k}` (i.e. `ℤ[1/n]` in the coordinate `x 0`). -/
lemma mem_dimGroup_full {n : ℕ} (hn : n ≠ 0) (x : Fin 1 → ℚ) :
    x ∈ dimGroup (full n) ↔ ∃ k : ℕ, x 0 * (n : ℚ) ^ k ∈ range (Int.cast : ℤ → ℚ) := by
  show (x ∈ eventualRange (full n) ∧ _) ↔ _
  rw [eventualRange_full hn]
  simp only [mem_univ, true_and, IsIntVec, vecMul_full, Fin.forall_fin_one, mem_range]
  exact exists_congr fun k => ⟨fun ⟨m, h⟩ => ⟨m, h.symm⟩, fun ⟨m, h⟩ => ⟨m, h.symm⟩⟩

/-- `G_[n]^+ = {x | x · n^k ∈ ℤ_{≥0} for some k}`. -/
lemma mem_dimCone_full {n : ℕ} (hn : n ≠ 0) (x : Fin 1 → ℚ) :
    x ∈ dimCone (full n) ↔ ∃ k : ℕ, x 0 * (n : ℚ) ^ k ∈ range (Nat.cast : ℕ → ℚ) := by
  show (x ∈ eventualRange (full n) ∧ _) ↔ _
  rw [eventualRange_full hn]
  simp only [mem_univ, true_and, IsNatVec, vecMul_full, Fin.forall_fin_one, mem_range]
  exact exists_congr fun k => ⟨fun ⟨m, h⟩ => ⟨m, h.symm⟩, fun ⟨m, h⟩ => ⟨m, h.symm⟩⟩

lemma two_four (S : Set ℚ) (hS : ∀ q ∈ S, ∀ j : ℕ, q * 2 ^ j ∈ S) (q : ℚ) :
    (∃ k : ℕ, q * (2 : ℕ) ^ k ∈ S) ↔ (∃ k : ℕ, q * (4 : ℕ) ^ k ∈ S) := by
  constructor
  · rintro ⟨k, hk⟩
    have e : q * ((4 : ℕ) : ℚ) ^ k = q * ((2 : ℕ) : ℚ) ^ k * 2 ^ k := by
      push_cast; rw [mul_assoc, ← mul_pow]; norm_num
    exact ⟨k, e ▸ hS _ hk k⟩
  · rintro ⟨k, hk⟩
    have e : q * ((2 : ℕ) : ℚ) ^ (2 * k) = q * ((4 : ℕ) : ℚ) ^ k := by
      push_cast; rw [pow_mul]; norm_num
    exact ⟨2 * k, e ▸ hk⟩

lemma dimGroup_two_eq_four : dimGroup (full 2) = dimGroup (full 4) := by
  ext x
  rw [mem_dimGroup_full (by norm_num), mem_dimGroup_full (by norm_num)]
  refine two_four _ (fun q hq j => ?_) _
  obtain ⟨m, hm⟩ := hq
  exact ⟨m * 2 ^ j, by push_cast; rw [hm]⟩

lemma dimCone_two_eq_four : dimCone (full 2) = dimCone (full 4) := by
  ext x
  rw [mem_dimCone_full (by norm_num), mem_dimCone_full (by norm_num)]
  refine two_four _ (fun q hq j => ?_) _
  obtain ⟨m, hm⟩ := hq
  exact ⟨m * 2 ^ j, by push_cast; rw [hm]⟩

/-- The dimension groups of the full 2-shift and the full 4-shift are order-isomorphic. -/
theorem dimOrderIso_two_four : DimOrderIso (full 2) (full 4) :=
  ⟨AddEquiv.addSubgroupCongr dimGroup_two_eq_four, fun x => by
    rw [dimCone_two_eq_four, AddEquiv.addSubgroupCongr_apply]⟩

/-! ## Main results -/

/-- The full 2-shift and the full 4-shift: mixing SFTs with order-isomorphic dimension groups
that are not orbit equivalent. -/
theorem counterexample :
    IsSFT (edgeShift (full 2)) ∧ IsSFT (edgeShift (full 4)) ∧
    IsMixing (edgeShift (full 2)) ∧ IsMixing (edgeShift (full 4)) ∧
    DimOrderIso (full 2) (full 4) ∧
    ¬ OrbitEquivalent (edgeShift (full 2)) (edgeShift (full 4)) :=
  ⟨isSFT_full 1, isSFT_full 3, isMixing_full 2, isMixing_full 4, dimOrderIso_two_four,
    not_orbitEquivalent_full (by norm_num)⟩

/-- The first clause of the conjecture, for mixing SFTs presented as edge shifts `X_A`. -/
def OEDimCriterion : Prop :=
  ∀ (r s : ℕ) (A : Matrix (Fin r) (Fin r) ℕ) (B : Matrix (Fin s) (Fin s) ℕ),
    IsMixing (edgeShift A) → IsMixing (edgeShift B) →
      (OrbitEquivalent (edgeShift A) (edgeShift B) ↔ DimOrderIso A B)

/-- The "if" direction fails, hence the criterion fails. -/
theorem not_OEDimCriterion : ¬ OEDimCriterion := fun h =>
  not_orbitEquivalent_full (m := 2) (n := 4) (by norm_num)
    ((h 1 1 (full 2) (full 4) (isMixing_full 2) (isMixing_full 4)).mpr dimOrderIso_two_four)

/-- The conjecture is a conjunction whose first clause is `OEDimCriterion`; it is false whatever
the other two clauses (entropy, Kakutani-Rokhlin realizability) mean. -/
theorem conjecture_false (entropyClause krClause : Prop) :
    ¬ (OEDimCriterion ∧ entropyClause ∧ krClause) := fun h => not_OEDimCriterion h.1

end C9629
