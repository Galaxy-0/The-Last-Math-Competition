import Mathlib

/-!
# Conjecture 00000001756: unimodular submatrices of the character table of `S_n`

A unimodular submatrix of the character table of `S_n` is a square submatrix with determinant
`±1`; `d(n)` is the maximal order of such a submatrix. The conjecture asserts
`d(n) = #{λ ⊢ n : the hook lengths of λ are pairwise coprime}`.

We refute it at `n = 3`.
* **Character table.** We build the trivial, sign and standard (`2`-dimensional: the sum-zero
  plane of the permutation representation) representations of `S_3` as objects of
  `FDRep ℂ (Equiv.Perm (Fin 3))`, compute their characters (`1`, `sgn`, `fix - 1`), and prove that
  they are irreducible (`Simple`, via Mathlib's `FDRep.simple_iff_char_is_norm_one`), pairwise
  non-isomorphic, and that every irreducible complex representation is isomorphic to one of them
  (via Mathlib's `FDRep.char_orthonormal`). `IsCharTable X` says that `X` is a character table:
  rows are the characters of a complete irredundant list of irreducibles, and columns are a
  complete irredundant list of conjugacy classes, in any order. Every such `X` has maximal
  unimodular order `2`: it has a `2 × 2` minor `-1`, and every `3 × 3` submatrix has determinant
  `±6`.
* **Hook count.** Every partition of `3` (as a Mathlib `Nat.Partition`) has pairwise coprime hook
  lengths, computed on its Ferrers diagram (a Mathlib `YoungDiagram`), so the formula gives `3`.

The Ferrers-diagram construction (`rowsAtLeast`, `ferrers`) is adapted from the accepted
solution of conjecture 00000000428 by C0ldSmi1e (GPL-3.0).
-/

open Matrix Finset CategoryTheory

namespace C1756

/-! ### Partitions, Ferrers diagrams and hook lengths -/

/-- The number of parts of `p` that are at least `k`. -/
def rowsAtLeast {n : ℕ} (p : Nat.Partition n) (k : ℕ) : ℕ := (p.parts.filter (k ≤ ·)).card

lemma rowsAtLeast_le {n : ℕ} (p : Nat.Partition n) (k : ℕ) : rowsAtLeast p k ≤ n := by
  have h := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) (fun a ha => p.parts_pos ha)
  simp only [smul_eq_mul, mul_one, p.parts_sum] at h
  exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans h

lemma rowsAtLeast_antitone {n : ℕ} (p : Nat.Partition n) : Antitone (rowsAtLeast p) :=
  fun _ _ hab => Multiset.card_le_card (Multiset.monotone_filter_right p.parts
    (fun _ hc => hab.trans hc))

/-- The Ferrers diagram of `p`: cell `(i, j)` (row `i`, column `j`) is present iff at least
`i + 1` parts are `≥ j + 1`. -/
def ferrers {n : ℕ} (p : Nat.Partition n) : YoungDiagram where
  cells := ((range n) ×ˢ (range n)).filter (fun c => c.1 < rowsAtLeast p (c.2 + 1))
  isLowerSet := by
    intro a b hab hb
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb ⊢
    refine ⟨⟨hab.1.trans_lt hb.1.1, hab.2.trans_lt hb.1.2⟩, ?_⟩
    exact hab.1.trans_lt (hb.2.trans_le (rowsAtLeast_antitone p (Nat.add_le_add_right hab.2 1)))

/-- The hook length of cell `c` in `μ`: arm (cells to the right) + leg (cells below) + 1. -/
def hookLength (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (μ.cells.filter fun d => d.1 = c.1 ∧ c.2 < d.2).card +
    (μ.cells.filter fun d => d.2 = c.2 ∧ c.1 < d.1).card + 1

/-- The hook lengths of `μ` are pairwise coprime (over pairs of distinct cells). -/
def HookCoprime (μ : YoungDiagram) : Prop :=
  ∀ c ∈ μ.cells, ∀ d ∈ μ.cells, c ≠ d → Nat.Coprime (hookLength μ c) (hookLength μ d)

instance (μ : YoungDiagram) : Decidable (HookCoprime μ) := by
  unfold HookCoprime; infer_instance

/-- The right-hand side of the conjecture: `#{λ ⊢ n : hook(λ) pairwise coprime}`. -/
def hookCount (n : ℕ) : ℕ := (univ.filter fun p : Nat.Partition n => HookCoprime (ferrers p)).card

/-- The three partitions of `3`. -/
def P3 : Nat.Partition 3 := ⟨{3}, by simp, by simp⟩
def P21 : Nat.Partition 3 := ⟨{2, 1}, by simp, by simp⟩
def P111 : Nat.Partition 3 := ⟨{1, 1, 1}, by simp, by simp⟩

theorem parts_three (p : Nat.Partition 3) :
    p.parts = {3} ∨ p.parts = {2, 1} ∨ p.parts = {1, 1, 1} := by
  obtain ⟨s, hpos, hsum⟩ := p
  show s = {3} ∨ s = {2, 1} ∨ s = {1, 1, 1}
  revert hpos hsum
  induction s using Quotient.inductionOn with
  | h l =>
    intro hpos hsum
    have hp : ∀ i ∈ l, 0 < i := fun i hi => hpos (by simpa using hi)
    simp only [Multiset.quot_mk_to_coe, Multiset.sum_coe] at hsum ⊢
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
    · simp at hsum
    · simp at hsum; subst hsum; decide
    · have ha := hp a (by simp); have hb := hp b (by simp)
      simp at hsum
      rcases (by omega : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        decide
    · have ha := hp a (by simp); have hb := hp b (by simp); have hc := hp c (by simp)
      simp at hsum
      obtain ⟨rfl, rfl, rfl⟩ : a = 1 ∧ b = 1 ∧ c = 1 := by omega
      decide
    · have ha := hp a (by simp); have hb := hp b (by simp); have hc := hp c (by simp)
      have hd := hp d (by simp)
      simp at hsum; omega

theorem partitions_three (p : Nat.Partition 3) : p = P3 ∨ p = P21 ∨ p = P111 := by
  rcases parts_three p with h | h | h
  · exact Or.inl (Nat.Partition.ext h)
  · exact Or.inr (Or.inl (Nat.Partition.ext h))
  · exact Or.inr (Or.inr (Nat.Partition.ext h))

theorem univ_partitions_three : (univ : Finset (Nat.Partition 3)) = {P3, P21, P111} := by
  ext p; simp only [mem_univ, mem_insert, mem_singleton, true_iff]; exact partitions_three p

/-- The Ferrers diagrams of the partitions of `3`. -/
theorem ferrers_P3 : (ferrers P3).cells = {(0, 0), (0, 1), (0, 2)} := by decide
theorem ferrers_P21 : (ferrers P21).cells = {(0, 0), (0, 1), (1, 0)} := by decide
theorem ferrers_P111 : (ferrers P111).cells = {(0, 0), (1, 0), (2, 0)} := by decide

/-- Hook lengths: `(3) ↦ 3, 2, 1`; `(2,1) ↦ 3, 1, 1`; `(1,1,1) ↦ 3, 2, 1`. -/
theorem hooks_P3 : (hookLength (ferrers P3) (0, 0), hookLength (ferrers P3) (0, 1),
    hookLength (ferrers P3) (0, 2)) = (3, 2, 1) := by decide
theorem hooks_P21 : (hookLength (ferrers P21) (0, 0), hookLength (ferrers P21) (0, 1),
    hookLength (ferrers P21) (1, 0)) = (3, 1, 1) := by decide
theorem hooks_P111 : (hookLength (ferrers P111) (0, 0), hookLength (ferrers P111) (1, 0),
    hookLength (ferrers P111) (2, 0)) = (3, 2, 1) := by decide

/-- Every partition of `3` has pairwise coprime hook lengths. -/
theorem hookCoprime_all (p : Nat.Partition 3) : HookCoprime (ferrers p) := by
  rcases partitions_three p with rfl | rfl | rfl <;> decide

theorem hookCount_three : hookCount 3 = 3 := by
  rw [hookCount, filter_true_of_mem (fun p _ => hookCoprime_all p), univ_partitions_three]
  decide

/-! ### Characters, classes and the integer table -/

abbrev G := Equiv.Perm (Fin 3)

/-- Number of fixed points of a permutation. -/
def fixCount (σ : G) : ℕ := (univ.filter fun x => σ x = x).card

/-- The characters of `irr 0, irr 1, irr 2` (proved in `irr_character`): `1`, `sgn`, `fix - 1`. -/
def chi : Fin 3 → G → ℤ
  | 0 => fun _ => 1
  | 1 => fun σ => (Equiv.Perm.sign σ : ℤ)
  | 2 => fun σ => (fixCount σ : ℤ) - 1

/-- Representatives of the conjugacy classes: identity, a transposition, a 3-cycle. -/
def rep : Fin 3 → G
  | 0 => 1
  | 1 => Equiv.swap 0 1
  | 2 => finRotate 3

/-- The integer table `chi i (rep j)`. Every character table of `S_3` is a row and column
permutation of it (`IsCharTable.reindex`). -/
def charTable : Matrix (Fin 3) (Fin 3) ℤ := fun i j => chi i (rep j)

theorem charTable_eq : charTable = !![1, 1, 1; 1, -1, 1; 2, 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-! ### The irreducible representations of `S_3` -/

/-- An integer matrix representation `G →* GL_n(ℤ)`, viewed as a complex representation on
`Fin n → ℂ`. -/
noncomputable def matRep {n : ℕ} (f : G →* Matrix (Fin n) (Fin n) ℤ) : FDRep ℂ G :=
  FDRep.of ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _).toMonoidHom.comp
    ((Int.castRingHom ℂ).mapMatrix.toMonoidHom.comp f))

theorem matRep_character {n : ℕ} (f : G →* Matrix (Fin n) (Fin n) ℤ) (g : G) :
    (matRep f).character g = ((f g).trace : ℂ) := by
  change LinearMap.trace ℂ _ (Matrix.toLin' ((f g).map (Int.castRingHom ℂ))) = _
  rw [Matrix.trace_toLin'_eq]
  simp [Matrix.trace]

/-- The `1 × 1` matrices of the trivial and sign representations. -/
def trivHom : G →* Matrix (Fin 1) (Fin 1) ℤ := 1

def signMat (σ : G) : Matrix (Fin 1) (Fin 1) ℤ := !![(Equiv.Perm.sign σ : ℤ)]

def signHom : G →* Matrix (Fin 1) (Fin 1) ℤ where
  toFun := signMat
  map_one' := by decide
  map_mul' := by decide

/-- The standard representation: `S_3` permutes `e₀, e₁, e₂`; on the invariant plane
`x + y + z = 0` we use the basis `f_j = e_j - e₂` (`j = 0, 1`). A vector of that plane has
coordinates `(x, y)` in this basis, so column `j` of `stdMat σ` is `(e_{σ j} - e_{σ 2})` restricted
to the first two coordinates. -/
def stdMat (σ : G) : Matrix (Fin 2) (Fin 2) ℤ := fun i j =>
  (if σ j.castSucc = i.castSucc then 1 else 0) - (if σ 2 = i.castSucc then 1 else 0)

def stdHom : G →* Matrix (Fin 2) (Fin 2) ℤ where
  toFun := stdMat
  map_one' := by decide
  map_mul' := by decide

/-- The three representations. -/
noncomputable def irr : Fin 3 → FDRep ℂ G
  | 0 => matRep trivHom
  | 1 => matRep signHom
  | 2 => matRep stdHom

theorem irr_character (i : Fin 3) (g : G) : (irr i).character g = (chi i g : ℂ) := by
  have h0 : ∀ g : G, (trivHom g).trace = chi 0 g := by decide
  have h1 : ∀ g : G, (signHom g).trace = chi 1 g := by decide
  have h2 : ∀ g : G, (stdHom g).trace = chi 2 g := by decide
  fin_cases i
  · simp only [irr, matRep_character, h0]; rfl
  · simp only [irr, matRep_character, h1]; rfl
  · simp only [irr, matRep_character, h2]; rfl

theorem card_G : Nat.card G = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl

noncomputable instance : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (by rw [card_G]; norm_num)

/-- Each of the three representations is irreducible (`Simple` in `FDRep ℂ S_3`). -/
theorem irr_simple (i : Fin 3) : Simple (irr i) := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have h : ∀ i : Fin 3, ∑ g : G, chi i g * chi i g⁻¹ = 6 := by decide
  simp only [irr_character, card_G]
  exact_mod_cast h i

/-! ### Completeness: every irreducible representation is one of the three -/

/-- The conjugacy class index of a permutation (`id`, transposition, 3-cycle). -/
def cls (g : G) : Fin 3 := if fixCount g = 3 then 0 else if fixCount g = 1 then 1 else 2

theorem cls_spec (g : G) : ∃ h : G, h * rep (cls g) * h⁻¹ = g := by revert g; decide

theorem cls_conj {a b : G} (h : IsConj a b) : cls a = cls b := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  revert a c; decide

theorem cls_rep (j : Fin 3) : cls (rep j) = j := by revert j; decide

theorem isConj_rep_cls (g : G) : IsConj g (rep (cls g)) := by
  obtain ⟨h, hh⟩ := cls_spec g
  exact (isConj_iff.mpr ⟨h, hh⟩).symm

/-- The representatives meet every conjugacy class exactly once. -/
theorem rep_complete (g : G) : ∃ j, IsConj (rep j) g := ⟨cls g, (isConj_rep_cls g).symm⟩

theorem rep_distinct (i j : Fin 3) (h : IsConj (rep i) (rep j)) : i = j := by
  rw [← cls_rep i, ← cls_rep j, cls_conj h]

theorem character_cls (V : FDRep ℂ G) (g : G) : V.character g = V.character (rep (cls g)) := by
  obtain ⟨h, hh⟩ := cls_spec g
  conv_lhs => rw [← hh]
  exact FDRep.char_conj _ _ _

/-- The class sums `|C_j| χ_i(C_j)`. -/
def classMat : Fin 3 → Fin 3 → ℤ := ![![1, 3, 2], ![1, -3, 2], ![2, 0, -2]]

theorem classSums : ∀ i j : Fin 3, ∑ g ∈ univ.filter (fun g => cls g = j), chi i g⁻¹ =
    classMat i j := by decide

theorem sum_classFun (F : Fin 3 → ℂ) (i : Fin 3) :
    ∑ g : G, F (cls g) * (chi i g⁻¹ : ℂ) =
      ∑ j : Fin 3, F j * (classMat i j : ℂ) := by
  rw [← Finset.sum_fiberwise univ cls (fun g => F (cls g) * (chi i g⁻¹ : ℂ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← classSums, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [(Finset.mem_filter.mp hg).2]

/-- **Completeness.** Every irreducible complex representation of `S_3` is isomorphic to one of
`irr 0, irr 1, irr 2`: otherwise its character is orthogonal to the three characters, hence `0`
on all three classes, contradicting `⟨χ, χ⟩ = 1`. -/
theorem irr_complete (V : FDRep ℂ G) [Simple V] : ∃ i, Nonempty (V ≅ irr i) := by
  by_contra hne'
  have hne : ∀ i, ¬ Nonempty (V ≅ irr i) := fun i h => hne' ⟨i, h⟩
  have horth : ∀ i, ∑ j : Fin 3, V.character (rep j) *
      (classMat i j : ℂ) = 0 := by
    intro i
    have := irr_simple i
    have h := FDRep.char_orthonormal V (irr i)
    rw [if_neg (hne i), card_G] at h
    rw [← sum_classFun]
    simpa [irr_character, ← character_cls] using h
  have h0 := horth 0; have h1 := horth 1; have h2 := horth 2
  simp [Fin.sum_univ_three, classMat] at h0 h1 h2
  have hb : V.character (rep 1) = 0 := by linear_combination (h0 - h1) / 6
  have hc : V.character (rep 2) = 0 := by linear_combination (h0 + h1 - h2) / 6
  have ha : V.character (rep 0) = 0 := by linear_combination h2 / 2 + hc
  have hz : ∀ g, V.character g = 0 := fun g => by
    rw [character_cls]; generalize cls g = j; fin_cases j <;> assumption
  have hs := (FDRep.simple_iff_char_is_norm_one V).mp inferInstance
  simp [hz, Fintype.card_perm, Nat.factorial] at hs

theorem irr_distinct (i j : Fin 3) (h : Nonempty (irr i ≅ irr j)) : i = j := by
  have hc := FDRep.char_iso h.some
  have key : ∀ i j : Fin 3, (∀ g : G, chi i g = chi j g) → i = j := by decide
  refine key i j fun g => ?_
  have := (irr_character i g).symm.trans ((congrFun hc g).trans (irr_character j g))
  exact_mod_cast this

/-! ### Character tables of `S_3` -/

/-- `X` is a character table of `S_3`: row `i` is the character of `V i` and column `j` the
conjugacy class of `g j`, where `V` lists every irreducible complex representation exactly once up
to isomorphism and `g` lists every conjugacy class exactly once, both in any order. -/
def IsCharTable {m m' : ℕ} (X : Matrix (Fin m) (Fin m') ℂ) : Prop :=
  ∃ (V : Fin m → FDRep ℂ G) (g : Fin m' → G),
    (∀ i, Simple (V i)) ∧ (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
    (∀ W : FDRep ℂ G, Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
    (∀ j j', IsConj (g j) (g j') → j = j') ∧ (∀ x : G, ∃ j, IsConj (g j) x) ∧
    ∀ i j, X i j = (V i).character (g j)

/-- Every character table is the integer table `charTable` with rows and columns permuted. -/
theorem IsCharTable.reindex {m m' : ℕ} {X : Matrix (Fin m) (Fin m') ℂ} (hX : IsCharTable X) :
    ∃ (π : Fin m ≃ Fin 3) (τ : Fin m' ≃ Fin 3), ∀ i j, X i j = (charTable (π i) (τ j) : ℂ) := by
  obtain ⟨V, g, hV, hVd, hVc, hgd, hgc, hX⟩ := hX
  choose π hπ using fun i => @irr_complete (V i) (hV i)
  have hπb : Function.Bijective π := by
    refine ⟨fun i j h => hVd i j ⟨(hπ i).some ≪≫ eqToIso (congrArg irr h) ≪≫ (hπ j).some.symm⟩,
      fun p => ?_⟩
    obtain ⟨i, ⟨e⟩⟩ := hVc (irr p) (irr_simple p)
    exact ⟨i, irr_distinct _ _ ⟨(hπ i).some.symm ≪≫ e.symm⟩⟩
  have hτb : Function.Bijective (fun j => cls (g j)) := by
    refine ⟨fun j j' h => hgd j j' ?_, fun p => ?_⟩
    · have h' : rep (cls (g j)) = rep (cls (g j')) := congrArg rep h
      exact (isConj_rep_cls (g j)).trans (h' ▸ (isConj_rep_cls (g j')).symm)
    · obtain ⟨j, hj⟩ := hgc (rep p)
      exact ⟨j, (cls_conj hj).trans (cls_rep p)⟩
  refine ⟨Equiv.ofBijective π hπb, Equiv.ofBijective _ hτb, fun i j => ?_⟩
  rw [hX, FDRep.char_iso (hπ i).some, character_cls, irr_character]
  rfl

/-- The character table of the constructed irreducibles `irr` at the representatives `rep`. -/
noncomputable def trueTable : Matrix (Fin 3) (Fin 3) ℂ := fun i j => (irr i).character (rep j)

theorem isCharTable_trueTable : IsCharTable trueTable :=
  ⟨irr, rep, irr_simple, irr_distinct, fun W hW => @irr_complete W hW, rep_distinct,
    rep_complete, fun _ _ => rfl⟩

theorem trueTable_eq : trueTable = !![1, 1, 1; 1, -1, 1; 2, 0, -1] := by
  ext i j
  have h : trueTable i j = (charTable i j : ℂ) := irr_character i (rep j)
  rw [h, charTable_eq]
  fin_cases i <;> fin_cases j <;> simp

/-! ### Unimodular submatrices and `d(3)` -/

/-- `M` has a unimodular square submatrix of order `k`: rows `r` and columns `c` (injective
selections) with determinant `±1`. -/
def IsUnimodularOrder {R : Type*} [CommRing R] {m n : ℕ} (M : Matrix (Fin m) (Fin n) R)
    (k : ℕ) : Prop :=
  ∃ (r : Fin k → Fin m) (c : Fin k → Fin n), Function.Injective r ∧ Function.Injective c ∧
    ((M.submatrix r c).det = 1 ∨ (M.submatrix r c).det = -1)

/-- The maximal order of a unimodular square submatrix. -/
noncomputable def maxUnimodularOrder {R : Type*} [CommRing R] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) R) : ℕ :=
  sSup {k | IsUnimodularOrder M k}

theorem det_charTable : charTable.det = 6 := by
  rw [charTable_eq, det_fin_three]; simp

/-- Every `3 × 3` submatrix (rows and columns permuted) has determinant `±6`. -/
theorem det_full_submatrix (r c : Fin 3 → Fin 3) (hr : Function.Injective r)
    (hc : Function.Injective c) :
    (charTable.submatrix r c).det = 6 ∨ (charTable.submatrix r c).det = -6 := by
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective r (Finite.injective_iff_bijective.mp hr)
  let f : Equiv.Perm (Fin 3) := Equiv.ofBijective c (Finite.injective_iff_bijective.mp hc)
  have hsub : charTable.submatrix r c = (charTable.submatrix e id).submatrix id f := by
    ext i j; rfl
  rw [hsub, det_permute', det_permute, det_charTable]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign f) with h2 | h2 <;> simp [h1, h2]

theorem unimodular_two : IsUnimodularOrder charTable 2 := by
  refine ⟨![0, 2], ![1, 2], by decide, by decide, Or.inr ?_⟩
  rw [det_fin_two, charTable_eq]; simp

theorem unimodular_le_two {k : ℕ} (h : IsUnimodularOrder charTable k) : k ≤ 2 := by
  obtain ⟨r, c, hr, hc, hdet⟩ := h
  have hk : k ≤ 3 := by simpa using Fintype.card_le_of_injective r hr
  by_contra hk2
  obtain rfl : k = 3 := by omega
  rcases det_full_submatrix r c hr hc with h | h <;> rw [h] at hdet <;> omega

/-- Minors of a permuted, complexified copy of `charTable` are casts of minors of `charTable`. -/
theorem det_reindex {m m' k : ℕ} {X : Matrix (Fin m) (Fin m') ℂ} {π : Fin m → Fin 3}
    {τ : Fin m' → Fin 3} (hX : ∀ i j, X i j = (charTable (π i) (τ j) : ℂ))
    (r : Fin k → Fin m) (c : Fin k → Fin m') :
    (X.submatrix r c).det = ((charTable.submatrix (π ∘ r) (τ ∘ c)).det : ℂ) := by
  have h := (Int.castRingHom ℂ).map_det (charTable.submatrix (π ∘ r) (τ ∘ c))
  rw [eq_intCast] at h
  rw [h]; congr 1; ext a b; simp [hX]

theorem isUnimodularOrder_reindex {m m' : ℕ} {X : Matrix (Fin m) (Fin m') ℂ}
    (π : Fin m ≃ Fin 3) (τ : Fin m' ≃ Fin 3) (hX : ∀ i j, X i j = (charTable (π i) (τ j) : ℂ))
    (k : ℕ) : IsUnimodularOrder X k ↔ IsUnimodularOrder charTable k := by
  have hcast : ∀ d : ℤ, ((d : ℂ) = 1 ∨ (d : ℂ) = -1) ↔ (d = 1 ∨ d = -1) := fun d => by
    norm_cast
  constructor
  · rintro ⟨r, c, hr, hc, hd⟩
    rw [det_reindex hX] at hd
    exact ⟨π ∘ r, τ ∘ c, π.injective.comp hr, τ.injective.comp hc, (hcast _).mp hd⟩
  · rintro ⟨r, c, hr, hc, hd⟩
    refine ⟨π.symm ∘ r, τ.symm ∘ c, π.symm.injective.comp hr, τ.symm.injective.comp hc, ?_⟩
    have e1 : π ∘ π.symm ∘ r = r := by ext; simp
    have e2 : τ ∘ τ.symm ∘ c = c := by ext; simp
    rw [det_reindex hX, e1, e2]
    exact (hcast _).mpr hd

/-- **`d(3) = 2` for every character table of `S_3`**, in any order of rows and columns. -/
theorem maxUnimodularOrder_of_isCharTable {m m' : ℕ} {X : Matrix (Fin m) (Fin m') ℂ}
    (hX : IsCharTable X) : maxUnimodularOrder X = 2 := by
  obtain ⟨π, τ, h⟩ := hX.reindex
  have hs : {k | IsUnimodularOrder X k} = {k | IsUnimodularOrder charTable k} :=
    Set.ext (isUnimodularOrder_reindex π τ h)
  rw [maxUnimodularOrder, hs]
  exact IsGreatest.csSup_eq ⟨unimodular_two, fun _ hk => unimodular_le_two hk⟩

/-- `d(3)`, computed on the genuine character table `trueTable`. -/
noncomputable def d3 : ℕ := maxUnimodularOrder trueTable

theorem d3_eq_two : d3 = 2 := maxUnimodularOrder_of_isCharTable isCharTable_trueTable

/-- **Main theorem.** For the character table of `S_3`, `d(3) = 2`, while
`#{λ ⊢ 3 : hook lengths of λ pairwise coprime} = 3`; so the conjectured formula fails at `n = 3`. -/
theorem conjecture_1756_false : d3 = 2 ∧ hookCount 3 = 3 ∧ d3 ≠ hookCount 3 := by
  refine ⟨d3_eq_two, hookCount_three, ?_⟩
  rw [d3_eq_two, hookCount_three]; decide

/-- The same refutation for every character table of `S_3`, in any row and column order. -/
theorem conjecture_1756_false_any_table {m m' : ℕ} (X : Matrix (Fin m) (Fin m') ℂ)
    (hX : IsCharTable X) : maxUnimodularOrder X = 2 ∧ hookCount 3 = 3 ∧
      maxUnimodularOrder X ≠ hookCount 3 := by
  rw [maxUnimodularOrder_of_isCharTable hX, hookCount_three]; decide

end C1756
