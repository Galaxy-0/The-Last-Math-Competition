import Mathlib

namespace Conjecture9994

universe u

open CategoryTheory

/-! ## Definitions -/

section Defs

variable (k : Type u) [Field k]

/-- An `A`-module is finite-dimensional if it is finite-dimensional over `k` after restriction of
scalars along `algebraMap k A`. -/
def IsFinDimModule {A : Type u} [Ring A] [Algebra k A] (X : ModuleCat.{u} A) : Prop :=
  Module.Finite k ((ModuleCat.restrictScalars (algebraMap k A)).obj X)

/-- The (little) finitistic dimension: the supremum of the projective dimensions of the
finite-dimensional modules of finite projective dimension. -/
noncomputable def finitisticDimension (A : Type u) [Ring A] [Algebra k A] : WithBot ℕ∞ :=
  ⨆ (X : ModuleCat.{u} A) (_ : IsFinDimModule k X) (_ : projectiveDimension X ≠ ⊤),
    projectiveDimension X

/-- The literal Definition line: the supremum of the projective dimensions of all
finite-dimensional modules. -/
noncomputable def finitisticDimensionLit (A : Type u) [Ring A] [Algebra k A] : WithBot ℕ∞ :=
  ⨆ (X : ModuleCat.{u} A) (_ : IsFinDimModule k X), projectiveDimension X

/-- For a finite-dimensional algebra, "finite-dimensional" and "finitely generated" modules agree,
so `finitisticDimension` is the little finitistic dimension in its usual form. -/
theorem isFinDimModule_iff {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A]
    (X : ModuleCat.{u} A) : IsFinDimModule k X ↔ Module.Finite A X := by
  let _ : Module k X := Module.compHom X (algebraMap k A)
  have _ : IsScalarTower k A X := ⟨fun c a x => by
    change (c • a) • x = (algebraMap k A c) • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  constructor
  · intro h
    have _ : Module.Finite k X := h
    exact Module.Finite.of_restrictScalars_finite k A X
  · intro h
    exact (Module.Finite.trans A X : Module.Finite k X)

/-- The Loewy length: the smallest positive `L` with `J ^ L = 0`, `J = Ring.jacobson A` (viewed
as a `k`-submodule of `A`; powers are products of subspaces, i.e. spans of `L`-fold products). -/
noncomputable def loewyLength (A : Type u) [Ring A] [Algebra k A] : ℕ :=
  sInf {L : ℕ | 0 < L ∧ ((Ring.jacobson A).restrictScalars k) ^ L = ⊥}

/-- Reading (a): `findim A ≤ 2 · LL(A)` for every finite-dimensional `k`-algebra `A`. -/
def DoublingBound : Prop :=
  ∀ (A : Type u) [Ring A] [Algebra k A], Module.Finite k A →
    finitisticDimension k A ≤ ((2 * loewyLength k A : ℕ) : WithBot ℕ∞)

/-- Reading (b): `findim A` is bounded by some function of `LL(A)` alone. -/
def LoewyControlled : Prop :=
  ∃ f : ℕ → ℕ, ∀ (A : Type u) [Ring A] [Algebra k A], Module.Finite k A →
    finitisticDimension k A ≤ ((f (loewyLength k A) : ℕ) : WithBot ℕ∞)

/-- Reading (a) with the literal Definition line. -/
def DoublingBoundLit : Prop :=
  ∀ (A : Type u) [Ring A] [Algebra k A], Module.Finite k A →
    finitisticDimensionLit k A ≤ ((2 * loewyLength k A : ℕ) : WithBot ℕ∞)

/-- Reading (b) with the literal Definition line. -/
def LoewyControlledLit : Prop :=
  ∃ f : ℕ → ℕ, ∀ (A : Type u) [Ring A] [Algebra k A], Module.Finite k A →
    finitisticDimensionLit k A ≤ ((f (loewyLength k A) : ℕ) : WithBot ℕ∞)

end Defs

/-! ## The algebra `Λ = k A_{m+1} / J²` -/

section Algebra

variable (k : Type u) [Field k] (m : ℕ)

/-- The arrow space `k^m`: coordinate `i` is the coefficient of the arrow `α_i`, which satisfies
`e_i α_i e_{i+1} = α_i` for the vertex idempotents `e_0, ..., e_m`. -/
def Arr : Type u := Fin m → k

instance : AddCommGroup (Arr k m) := inferInstanceAs (AddCommGroup (Fin m → k))
instance : Module k (Arr k m) := inferInstanceAs (Module k (Fin m → k))
instance : Module.Finite k (Arr k m) := inferInstanceAs (Module.Finite k (Fin m → k))

/-- Left action of the vertex idempotents: `(r • μ)_i = r_i μ_i`. -/
instance : Module (Fin (m + 1) → k) (Arr k m) where
  smul r μ := fun i => r i.castSucc * (μ : Fin m → k) i
  one_smul _ := funext fun _ => one_mul _
  mul_smul _ _ _ := funext fun _ => mul_assoc _ _ _
  smul_zero _ := funext fun _ => mul_zero _
  smul_add _ _ _ := funext fun _ => mul_add _ _ _
  add_smul _ _ _ := funext fun _ => add_mul _ _ _
  zero_smul _ := funext fun _ => zero_mul _

/-- Right action of the vertex idempotents: `(μ <• r)_i = μ_i r_{i+1}`. -/
instance : Module (Fin (m + 1) → k)ᵐᵒᵖ (Arr k m) where
  smul r μ := fun i => (μ : Fin m → k) i * r.unop i.succ
  one_smul _ := funext fun _ => mul_one _
  mul_smul _ _ _ := funext fun _ => by
    change _ * ((_ : Fin (m + 1) → k) _ * _) = _ * _ * _; ring
  smul_zero _ := funext fun _ => zero_mul _
  smul_add _ _ _ := funext fun _ => add_mul _ _ _
  add_smul _ _ _ := funext fun _ => mul_add _ _ _
  zero_smul _ := funext fun _ => mul_zero _

variable {k m}

@[simp] theorem add_apply' (μ ν : Arr k m) (i : Fin m) :
    (μ + ν : Arr k m) i = (μ : Fin m → k) i + (ν : Fin m → k) i := rfl
@[simp] theorem zero_apply' (i : Fin m) : (0 : Arr k m) i = 0 := rfl
@[simp] theorem lsmul_apply (r : Fin (m + 1) → k) (μ : Arr k m) (i : Fin m) :
    (r • μ : Arr k m) i = r i.castSucc * (μ : Fin m → k) i := rfl
@[simp] theorem rsmul_apply (r : (Fin (m + 1) → k)ᵐᵒᵖ) (μ : Arr k m) (i : Fin m) :
    (r • μ : Arr k m) i = (μ : Fin m → k) i * r.unop i.succ := rfl
@[simp] theorem ksmul_apply (c : k) (μ : Arr k m) (i : Fin m) :
    (c • μ : Arr k m) i = c * (μ : Fin m → k) i := rfl

/-- The arrow vector `c α_i`. -/
def Arr.single (i : Fin m) (c : k) : Arr k m := Pi.single i c

@[simp] theorem Arr.single_apply (i l : Fin m) (c : k) :
    (Arr.single i c : Arr k m) l = if l = i then c else 0 := Pi.single_apply i c l

variable (k m)

instance : SMulCommClass (Fin (m + 1) → k) (Fin (m + 1) → k)ᵐᵒᵖ (Arr k m) :=
  ⟨fun _ _ _ => funext fun _ => by simp only [lsmul_apply, rsmul_apply]; ring⟩

instance : IsScalarTower k (Fin (m + 1) → k) (Arr k m) := by
  refine ⟨fun c r μ => funext fun i => ?_⟩
  change (c • r) i.castSucc * (μ : Fin m → k) i = c * (r i.castSucc * (μ : Fin m → k) i)
  simp only [Pi.smul_apply, smul_eq_mul]; ring

instance : IsScalarTower k (Fin (m + 1) → k)ᵐᵒᵖ (Arr k m) := by
  refine ⟨fun c r μ => funext fun i => ?_⟩
  change (μ : Fin m → k) i * (c • r).unop i.succ = c * ((μ : Fin m → k) i * r.unop i.succ)
  simp only [MulOpposite.unop_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- The witness algebra: the trivial square-zero extension of the vertex algebra `k^{m+1}` by the
arrow bimodule `k^m`. It has `k`-basis `e_0, ..., e_m, α_0, ..., α_{m-1}`, with `e_i e_j = δ_ij e_i`,
`e_i α_i e_{i+1} = α_i` and all products of two arrows zero, i.e. it is the radical-square-zero
algebra of the linear quiver with `m + 1` vertices. (This description is not used in the proofs.) -/
abbrev Alg : Type u := TrivSqZeroExt (Fin (m + 1) → k) (Arr k m)

instance : Module.Finite k (Alg k m) :=
  inferInstanceAs (Module.Finite k ((Fin (m + 1) → k) × Arr k m))

end Algebra

/-! ## Simple and projective modules -/

section Modules

variable {k : Type u} [Field k] {m : ℕ}

/-- Products of radical elements vanish. -/
theorem mul_eq_zero_of_fst {a b : Alg k m} (ha : a.fst = 0) (hb : b.fst = 0) : a * b = 0 := by
  ext1
  · simp [ha]
  · simp [ha, hb]

variable (k m)

/-- The simple module `S_j = k` at vertex `j`: `a • x = a_j x`. -/
def Sim (_ : Fin (m + 1)) : Type u := k

instance (j : Fin (m + 1)) : AddCommGroup (Sim k m j) := inferInstanceAs (AddCommGroup k)
instance (j : Fin (m + 1)) : Module k (Sim k m j) := inferInstanceAs (Module k k)
instance (j : Fin (m + 1)) : Nontrivial (Sim k m j) := inferInstanceAs (Nontrivial k)

/-- Evaluation of the vertex part at `j`, a ring homomorphism `Λ → k`. -/
noncomputable def ev (j : Fin (m + 1)) : Alg k m →+* k :=
  (Pi.evalRingHom (fun _ => k) j).comp
    (TrivSqZeroExt.fstHom k (Fin (m + 1) → k) (Arr k m)).toRingHom

noncomputable instance (j : Fin (m + 1)) : Module (Alg k m) (Sim k m j) :=
  Module.compHom (Sim k m j) (ev k m j)

variable {k m}

/-- The underlying scalar of an element of `S_j`. -/
def Sim.val {j : Fin (m + 1)} (x : Sim k m j) : k := x
/-- An element of `S_j` from a scalar. -/
def Sim.mk (j : Fin (m + 1)) (c : k) : Sim k m j := c

omit [Field k] in
@[simp] theorem Sim.val_mk (j : Fin (m + 1)) (c : k) : (Sim.mk j c : Sim k m j).val = c := rfl
@[simp] theorem Sim.val_add {j : Fin (m + 1)} (x y : Sim k m j) : (x + y).val = x.val + y.val :=
  rfl
@[simp] theorem Sim.val_zero {j : Fin (m + 1)} : (0 : Sim k m j).val = 0 := rfl
omit [Field k] in
theorem Sim.ext {j : Fin (m + 1)} {x y : Sim k m j} (h : x.val = y.val) : x = y := h
@[simp] theorem Sim.val_smul {j : Fin (m + 1)} (a : Alg k m) (x : Sim k m j) :
    (a • x).val = a.fst j * x.val := rfl

/-- The action on `P_{i+1}` written on `k × k`. -/
def projSmul (i : Fin m) (a : Alg k m) (v : k × k) : k × k :=
  (a.fst i.succ * v.1, a.fst i.castSucc * v.2 + (a.snd : Fin m → k) i * v.1)

theorem projSmul_one (i : Fin m) (v : k × k) : projSmul i 1 v = v := by
  simp [projSmul]

theorem projSmul_mul (i : Fin m) (a b : Alg k m) (v : k × k) :
    projSmul i (a * b) v = projSmul i a (projSmul i b v) := by
  simp only [projSmul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, Pi.mul_apply, add_apply',
    lsmul_apply, rsmul_apply, MulOpposite.unop_op, Prod.mk.injEq]
  constructor <;> ring

theorem projSmul_add (i : Fin m) (a : Alg k m) (v w : k × k) :
    projSmul i a (v + w) = projSmul i a v + projSmul i a w := by
  simp only [projSmul, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

theorem projSmul_add_left (i : Fin m) (a b : Alg k m) (v : k × k) :
    projSmul i (a + b) v = projSmul i a v + projSmul i b v := by
  simp only [projSmul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, Pi.add_apply, add_apply',
    Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

theorem projSmul_zero (i : Fin m) (a : Alg k m) : projSmul i a (0 : k × k) = 0 := by
  simp [projSmul]

theorem projSmul_zero_left (i : Fin m) (v : k × k) : projSmul i (0 : Alg k m) v = 0 := by
  simp [projSmul]

variable (k m)

/-- The indecomposable projective `P_{i+1} = Λ e_{i+1} = k e_{i+1} ⊕ k α_i` (for `i < m`):
`a • (x, y) = (a_{i+1} x, a_i y + μ_i x)` where `a = (r, μ)`. -/
def Proj (_ : Fin m) : Type u := k × k

instance (i : Fin m) : AddCommGroup (Proj k m i) := inferInstanceAs (AddCommGroup (k × k))

instance (i : Fin m) : Module (Alg k m) (Proj k m i) where
  smul a v := projSmul i a v
  one_smul v := projSmul_one i v
  mul_smul a b v := projSmul_mul i a b v
  smul_zero a := projSmul_zero i a
  smul_add a v w := projSmul_add i a v w
  add_smul a b v := projSmul_add_left i a b v
  zero_smul v := projSmul_zero_left i v

variable {k m}

/-- The underlying pair of an element of `P_{i+1}`. -/
def Proj.val {i : Fin m} (v : Proj k m i) : k × k := v
/-- An element of `P_{i+1}` from a pair. -/
def Proj.mk (i : Fin m) (v : k × k) : Proj k m i := v

omit [Field k] in
@[simp] theorem Proj.val_mk (i : Fin m) (v : k × k) : (Proj.mk i v : Proj k m i).val = v := rfl
@[simp] theorem Proj.val_add {i : Fin m} (v w : Proj k m i) : (v + w).val = v.val + w.val := rfl
@[simp] theorem Proj.val_zero {i : Fin m} : (0 : Proj k m i).val = 0 := rfl
omit [Field k] in
theorem Proj.ext {i : Fin m} {v w : Proj k m i} (h : v.val = w.val) : v = w := h
@[simp] theorem Proj.val_smul {i : Fin m} (a : Alg k m) (v : Proj k m i) :
    (a • v).val = projSmul i a v.val := rfl

end Modules

/-! ## Projectivity and the short exact sequences -/

section Homological

variable {k : Type u} [Field k] {m : ℕ}

/-- `S_0 = Λ e_0` is projective: it is a retract of `Λ`. -/
theorem sim_zero_projective : Module.Projective (Alg k m) (Sim k m 0) := by
  let ι : Sim k m 0 →ₗ[Alg k m] Alg k m :=
    { toFun := fun x => TrivSqZeroExt.inl (Pi.single 0 x.val)
      map_add' := fun x y => by simp [Pi.single_add]
      map_smul' := fun a x => by
        rw [Sim.val_smul, RingHom.id_apply, smul_eq_mul]
        ext1
        · funext l
          by_cases hl : l = 0
          · subst hl; simp
          · simp [hl]
        · funext i
          simp }
  refine Module.Projective.of_split ι (LinearMap.toSpanSingleton _ _ (Sim.mk 0 1)) ?_
  refine LinearMap.ext fun x => Sim.ext ?_
  change (ι x).fst 0 * 1 = x.val
  simp [ι]

/-- `P_{i+1}` is projective: it is a retract of `Λ` (it is `Λ e_{i+1}`). -/
theorem proj_projective (i : Fin m) : Module.Projective (Alg k m) (Proj k m i) := by
  let ι : Proj k m i →ₗ[Alg k m] Alg k m :=
    { toFun := fun v => TrivSqZeroExt.inl (Pi.single i.succ v.val.1) +
        TrivSqZeroExt.inr (Arr.single i v.val.2)
      map_add' := fun v w => by
        ext1
        · simp [Pi.single_add]
        · funext l; simp [ite_add_ite]
      map_smul' := fun a v => by
        show _ = a * _
        ext1
        · funext l
          rw [TrivSqZeroExt.fst_mul]
          by_cases hl : l = i.succ
          · subst hl; simp [projSmul]
          · simp [projSmul, hl]
        · funext l
          rw [TrivSqZeroExt.snd_mul]
          by_cases hl : l = i
          · subst hl; simp [projSmul]
          · simp [projSmul, hl] }
  let π : Alg k m →ₗ[Alg k m] Proj k m i :=
    { toFun := fun a => Proj.mk i (a.fst i.succ, (a.snd : Fin m → k) i)
      map_add' := fun a b => rfl
      map_smul' := fun a b => Proj.ext (by
        simp only [Proj.val_mk, Proj.val_smul, projSmul, TrivSqZeroExt.fst_mul,
          TrivSqZeroExt.snd_mul, Pi.mul_apply, add_apply', lsmul_apply, rsmul_apply,
          MulOpposite.unop_op, RingHom.id_apply, smul_eq_mul]) }
  refine Module.Projective.of_split ι π ?_
  refine LinearMap.ext fun v => Proj.ext ?_
  change ((ι v).fst i.succ, (ι v).snd i) = v.val
  simp [ι]

/-- The inclusion `S_i → P_{i+1}`, `y ↦ (0, y)` (the socle `k α_i`). -/
def incl (i : Fin m) : Sim k m i.castSucc →ₗ[Alg k m] Proj k m i where
  toFun y := Proj.mk i (0, y.val)
  map_add' x y := Proj.ext (by simp)
  map_smul' a y := Proj.ext (by simp [projSmul])

/-- The projection `P_{i+1} → S_{i+1}`, `(x, y) ↦ x` (the top). -/
def proj (i : Fin m) : Proj k m i →ₗ[Alg k m] Sim k m i.succ where
  toFun v := Sim.mk _ v.val.1
  map_add' v w := Sim.ext (by simp)
  map_smul' a v := Sim.ext (by simp [projSmul])

/-- The short complex `0 → S_i → P_{i+1} → S_{i+1} → 0` in `ModuleCat Λ`. -/
noncomputable abbrev ses (i : Fin m) : ShortComplex (ModuleCat.{u} (Alg k m)) :=
  ModuleCat.shortComplexOfCompEqZero (incl i) (proj i)
    (LinearMap.ext fun y => Sim.ext (by simp [incl, proj]))

theorem ses_shortExact (i : Fin m) : (ses (k := k) i).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro (v : Proj k m i)
    change proj (k := k) i v = 0 ↔ v ∈ Set.range (incl (k := k) i)
    constructor
    · intro hv
      refine ⟨Sim.mk _ v.val.2, Proj.ext ?_⟩
      have h1 : v.val.1 = 0 := congrArg Sim.val hv
      simp [incl, ← h1]
    · rintro ⟨y, rfl⟩
      exact Sim.ext (by simp [incl, proj])
  · intro (x : Sim k m i.castSucc) (y : Sim k m i.castSucc) h
    have := congrArg (fun v : Proj k m i => v.val.2) (h : incl (k := k) i x = incl (k := k) i y)
    exact Sim.ext (by simpa [incl] using this)
  · intro (x : Sim k m i.succ)
    exact ⟨Proj.mk i (x.val, (0 : k)), Sim.ext (k := k) (by simp [proj])⟩

/-- `S_{i+1}` is not projective: a section of `P_{i+1} → S_{i+1}` would have to be killed by the
arrow `α_i`, which acts nontrivially on `P_{i+1}`. -/
theorem sim_succ_not_projective (i : Fin m) : ¬ Module.Projective (Alg k m) (Sim k m i.succ) := by
  intro hP
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (proj (k := k) i) LinearMap.id
    (fun x => ⟨Proj.mk i (x.val, (0 : k)), Sim.ext (by simp [proj])⟩)
  let b : Alg k m := TrivSqZeroExt.inr (Arr.single i 1)
  have h1 : b • Sim.mk i.succ (1 : k) = 0 := Sim.ext (by simp [b])
  have h2 : (s (Sim.mk i.succ (1 : k))).val.1 = 1 :=
    congrArg Sim.val (LinearMap.congr_fun hs (Sim.mk i.succ (1 : k)))
  have h3 := congrArg (fun v : Proj k m i => v.val.2) (s.map_smul b (Sim.mk i.succ (1 : k)))
  simp [h1, b, projSmul, h2] at h3

end Homological

/-! ## Projective dimensions of the simples -/

section Dimension

variable {k : Type u} [Field k] {m : ℕ}

variable (k m) in
/-- The simple module `S_j` as an object of `ModuleCat Λ`. -/
noncomputable abbrev S (j : Fin (m + 1)) : ModuleCat.{u} (Alg k m) := ModuleCat.of _ (Sim k m j)

/-- `pd S_j = j`, in the form `pd S_j < j + 1` and `¬ pd S_j < j`. -/
theorem pd_claim (j : Fin (m + 1)) :
    HasProjectiveDimensionLT (S k m j) (j.val + 1) ∧ ¬ HasProjectiveDimensionLT (S k m j) j.val := by
  induction j using Fin.induction with
  | zero =>
    refine ⟨?_, ?_⟩
    · exact projective_iff_hasProjectiveDimensionLT_one.1
        ((IsProjective.iff_projective _).1 sim_zero_projective)
    · rw [Fin.val_zero, hasProjectiveDimensionLT_zero_iff_isZero,
        ModuleCat.isZero_of_iff_subsingleton]
      exact not_subsingleton _
  | succ i ih =>
    have hP : Projective (ses (k := k) i).X₂ := (IsProjective.iff_projective _).1 (proj_projective i)
    have hS := ses_shortExact (k := k) i
    rw [Fin.val_succ]
    rw [Fin.val_castSucc] at ih
    refine ⟨(hS.hasProjectiveDimensionLT_X₃_iff i.val hP).2 ih.1, ?_⟩
    obtain h0 | ⟨n, hn⟩ : i.val = 0 ∨ ∃ n, i.val = n + 1 :=
      (Nat.eq_zero_or_pos _).imp id fun h => ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    · rw [h0]
      intro h
      exact sim_succ_not_projective i ((IsProjective.iff_projective _).2
        (projective_iff_hasProjectiveDimensionLT_one.2 h))
    · rw [hn] at ih ⊢
      exact fun h => ih.2 ((hS.hasProjectiveDimensionLT_X₃_iff n hP).1 h)

/-- `pd S_m = m` for the simple module at the last vertex `m`. -/
theorem pd_last : projectiveDimension (S k m (Fin.last m)) = m := by
  obtain ⟨h1, h2⟩ := pd_claim (k := k) (Fin.last m)
  rw [Fin.val_last] at h1 h2
  exact le_antisymm ((projectiveDimension_le_iff _ m).2 h1) ((projectiveDimension_ge_iff _ m).2 h2)

/-- Every `S_j` is finite-dimensional (it is one-dimensional over `k`). -/
theorem S_findim (j : Fin (m + 1)) : IsFinDimModule k (S k m j) := by
  unfold IsFinDimModule
  let f : k →ₗ[k] (ModuleCat.restrictScalars (algebraMap k (Alg k m))).obj (S k m j) :=
    { toFun := fun c => (Sim.mk j c : Sim k m j)
      map_add' := fun _ _ => rfl
      map_smul' := fun c d => by
        show Sim.mk j (c * d) = (algebraMap k (Alg k m) c) • (Sim.mk j d : Sim k m j)
        apply Sim.ext
        simp [TrivSqZeroExt.algebraMap_eq_inl'] }
  exact Module.Finite.of_surjective f (fun x => ⟨Sim.val (j := j) x, rfl⟩)

end Dimension

/-! ## The Jacobson radical and the Loewy length -/

section Loewy

variable {k : Type u} [Field k] {m : ℕ}

/-- The Jacobson radical of `Λ` is the arrow ideal `{a | a.fst = 0}`. -/
theorem mem_jacobson_iff (a : Alg k m) : a ∈ Ring.jacobson (Alg k m) ↔ a.fst = 0 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  constructor
  · intro h
    funext j
    by_contra hj
    obtain ⟨z, hz⟩ := h (TrivSqZeroExt.inl (Pi.single j (-(a.fst j)⁻¹)))
    rw [Submodule.mem_bot] at hz
    have h1 := congrArg (fun t : Alg k m => t.fst j) hz
    have h2 : z.fst j * -(a.fst j)⁻¹ * a.fst j + z.fst j - 1 = -1 := by
      field_simp [show a.fst j ≠ 0 from hj]; ring
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_one, TrivSqZeroExt.fst_zero, Pi.add_apply,
      Pi.sub_apply, Pi.mul_apply, Pi.single_eq_same, Pi.one_apply, Pi.zero_apply, h2] at h1
    exact one_ne_zero (neg_eq_zero.1 h1)
  · intro ha y
    refine ⟨1 - y * a, ?_⟩
    rw [Submodule.mem_bot]
    have hya : (y * a).fst = 0 := by simp [ha]
    calc (1 - y * a) * y * a + (1 - y * a) - 1 = -((y * a) * (y * a)) := by noncomm_ring
    _ = 0 := by rw [mul_eq_zero_of_fst hya hya, neg_zero]

/-- `J² = 0`. -/
theorem jacobson_sq : ((Ring.jacobson (Alg k m)).restrictScalars k) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Submodule.mul_le]
  intro a ha b hb
  rw [Submodule.mem_bot]
  exact mul_eq_zero_of_fst ((mem_jacobson_iff a).1 ha) ((mem_jacobson_iff b).1 hb)

/-- `J ≠ 0` as soon as there is an arrow. -/
theorem jacobson_ne_bot (hm : 0 < m) : (Ring.jacobson (Alg k m)).restrictScalars k ≠ ⊥ := by
  intro h
  have h1 : (TrivSqZeroExt.inr (Arr.single ⟨0, hm⟩ 1) : Alg k m) ∈
      (Ring.jacobson (Alg k m)).restrictScalars k := (mem_jacobson_iff _).2 (by simp)
  rw [h, Submodule.mem_bot] at h1
  have h2 := congrArg (fun t : Alg k m => (t.snd : Fin m → k) ⟨0, hm⟩) h1
  simp at h2

/-- The Loewy length of `Λ_{m+1}` is `2` (for `m ≥ 1`, i.e. at least two vertices). -/
theorem loewyLength_eq_two (hm : 0 < m) : loewyLength k (Alg k m) = 2 := by
  refine le_antisymm (Nat.sInf_le ⟨two_pos, jacobson_sq⟩)
    (le_csInf ⟨2, two_pos, jacobson_sq⟩ fun b ⟨hb0, hb⟩ => ?_)
  by_contra hlt
  obtain rfl : b = 1 := by omega
  exact jacobson_ne_bot hm (by simpa using hb)

end Loewy

/-! ## Main results -/

section Main

variable (k : Type u) [Field k]

/-- `findim Λ_{m+1} ≥ m` (standard definition). -/
theorem le_finitisticDimension (m : ℕ) : (m : WithBot ℕ∞) ≤ finitisticDimension k (Alg k m) := by
  have hpd := pd_last (k := k) (m := m)
  have hne : projectiveDimension (S k m (Fin.last m)) ≠ ⊤ := by
    refine (projectiveDimension_ne_top_iff _).2 ⟨m, ?_⟩
    have := (pd_claim (k := k) (Fin.last m)).1
    rwa [Fin.val_last] at this
  rw [← hpd]
  exact le_iSup_of_le (S k m (Fin.last m)) (le_iSup_of_le (S_findim _) (le_iSup_of_le hne le_rfl))

/-- The standard finitistic dimension is at most the literal one (smaller index set). -/
theorem finitisticDimension_le_lit (A : Type u) [Ring A] [Algebra k A] :
    finitisticDimension k A ≤ finitisticDimensionLit k A :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_le fun _ => le_rfl

/-- Casting `ℕ → WithBot ℕ∞` reflects `≤`. -/
theorem natCast_le_natCast {a b : ℕ} (h : (a : WithBot ℕ∞) ≤ (b : WithBot ℕ∞)) : a ≤ b := by
  exact_mod_cast h

/-- The infinite family: for every `m ≥ 1`, `LL(Λ_{m+1}) = 2` while `findim Λ_{m+1} ≥ m`. -/
theorem family (m : ℕ) (hm : 0 < m) :
    loewyLength k (Alg k m) = 2 ∧ (m : WithBot ℕ∞) ≤ finitisticDimension k (Alg k m) ∧
      (m : WithBot ℕ∞) ≤ finitisticDimensionLit k (Alg k m) :=
  ⟨loewyLength_eq_two hm, le_finitisticDimension k m,
    (le_finitisticDimension k m).trans (finitisticDimension_le_lit k _)⟩

/-- Headline instance `n = 6` vertices (`m = 5` arrows): `LL(Λ_6) = 2`, `pd S_5 = 5`, so
`findim Λ_6 ≥ 5 > 4 = 2 · LL(Λ_6)`. -/
theorem headline :
    loewyLength k (Alg k 5) = 2 ∧ projectiveDimension (S k 5 (Fin.last 5)) = 5 ∧
      (5 : WithBot ℕ∞) ≤ finitisticDimension k (Alg k 5) ∧
      ¬ finitisticDimension k (Alg k 5) ≤ ((2 * loewyLength k (Alg k 5) : ℕ) : WithBot ℕ∞) := by
  refine ⟨loewyLength_eq_two (by norm_num), pd_last, le_finitisticDimension k 5, fun h => ?_⟩
  rw [loewyLength_eq_two (by norm_num)] at h
  have := natCast_le_natCast ((le_finitisticDimension k 5).trans h)
  norm_num at this

theorem not_doublingBound : ¬ DoublingBound k := fun h => (headline k).2.2.2 (h _ inferInstance)

theorem not_loewyControlled : ¬ LoewyControlled k := fun ⟨f, hf⟩ => by
  have h1 := hf (Alg k (f 2 + 1)) inferInstance
  rw [loewyLength_eq_two (by omega)] at h1
  have := natCast_le_natCast ((le_finitisticDimension k (f 2 + 1)).trans h1)
  omega

theorem not_doublingBoundLit : ¬ DoublingBoundLit k := fun h => not_doublingBound k
  fun A _ _ hA => (finitisticDimension_le_lit k A).trans (h A hA)

theorem not_loewyControlledLit : ¬ LoewyControlledLit k := fun ⟨f, hf⟩ => not_loewyControlled k
  ⟨f, fun A _ _ hA => (finitisticDimension_le_lit k A).trans (hf A hA)⟩

/-- Main theorem. Over every field `k`, the conjecture fails under both readings of
"controlled by twice the Loewy length" (`findim ≤ 2 LL`, or `findim ≤ f(LL)` for some `f`), with
either the standard or the literal definition of the finitistic dimension, whatever the remaining
clauses (`Rest`) say. -/
theorem conjecture_9994_false (Rest : Prop) :
    ¬ (DoublingBound k ∧ Rest) ∧ ¬ (LoewyControlled k ∧ Rest) ∧
      ¬ (DoublingBoundLit k ∧ Rest) ∧ ¬ (LoewyControlledLit k ∧ Rest) :=
  ⟨fun h => not_doublingBound k h.1, fun h => not_loewyControlled k h.1,
    fun h => not_doublingBoundLit k h.1, fun h => not_loewyControlledLit k h.1⟩

end Main

end Conjecture9994
