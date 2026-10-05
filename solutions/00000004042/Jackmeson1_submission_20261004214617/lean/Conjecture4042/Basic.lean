import Mathlib

/-!
# Conjecture 00000004042 is false

Conjecture 00000004042 reads:

> Definition: An interval algebra is an algebra constructed from a poset with repdim = 3.
> Conjecture: The realizable values of repdim are dense above 3, and the class of algebras with
> repdim = 3 is closed under derived equivalence.

Here `repdim` is Auslander's representation dimension of a finite-dimensional algebra `A` over a
field `k`:

  `repdim A = inf { gl.dim End_A(M) : M a generator-cogenerator of mod A }`.

The conjecture is the conjunction of
* (1) `DenseAbove3`: the set of realizable values of `repdim` is dense in the half-line `(3, ∞)`
  (Mathlib's topological `Dense`, in the subspace `Set.Ioi 3` of `ℝ`);
* (2) `ClosedUnderDerivedEquivalence`: if `repdim A = 3` and `B` is derived equivalent to `A`
  (the derived categories are equivalent as triangulated categories), then `repdim B = 3`.

We refute (1), so the conjunction is false. This does not depend on how clause (2) is formalized:
`conjecture_00000004042_false_of_any_clause2` proves `¬ (DenseAbove3 ∧ P)` for *every* proposition
`P`, and the main theorem `conjecture_00000004042_false` is its instance at our formalization
`ClosedUnderDerivedEquivalence`. The "interval algebra" definition only introduces a name and
plays no role in either clause.

Definitions:
* `globalDimension R`: the supremum over all left `R`-modules `X` (objects of `ModuleCat.{u} R`) of
  Mathlib's `CategoryTheory.projectiveDimension X ∈ WithBot ℕ∞`;
* `DualRegular k A`: `D(A_A) = Hom_k(A, k)`, a left `A`-module via `(a • f)(x) = f (x * a)`;
* `IsSummandOfPower X M`: `X ∈ add M`, i.e. `X` is a direct summand of `M ^ n` for some `n`;
* `IsGeneratorCogenerator k A M`: `M` is finitely generated, `A ∈ add M` and `D(A) ∈ add M`;
* `repdim k A`: the infimum over generator-cogenerators `M` of `globalDimension (Module.End A M)`;
* `toEReal`: the order embedding `WithBot ℕ∞ → EReal` (`⊥ ↦ ⊥`, `n ↦ n`, `⊤ ↦ ⊤`);
* `IsRealizable v`: `v = repdim A` for some finite-dimensional algebra `A` over some field;
* `DerivedEquivalent A B`: a triangulated equivalence of Mathlib's derived categories.

Universes: the field `k`, the algebra `A`, the modules `M` and the modules over `End_A(M)` all live in
one universe `u` (every finitely generated `A`-module, and every cyclic `End_A(M)`-module, has an
isomorphic copy there). All statements are universe polymorphic and are refuted in every universe.

Proof: `repdim_eq_nat_of_toEReal_eq` (every finite value of `repdim` is a natural number, because
`repdim` is an infimum of global dimensions, i.e. of suprema of projective dimensions, all in
`WithBot ℕ∞`), `no_nat_in_Ioo` (no natural number lies in `(13/4, 15/4)`), `not_denseAbove3` (the
nonempty open subset `(13/4, 15/4)` of `(3, ∞)` contains no realizable value).
-/

namespace Conjecture4042

universe u

open CategoryTheory

/-! ## Global dimension and representation dimension -/

/-- The (left) global dimension of a ring `R`: the supremum of the projective dimensions of all
left `R`-modules, valued in `WithBot ℕ∞` (Mathlib's codomain of `projectiveDimension`). -/
noncomputable def globalDimension (R : Type u) [Ring R] : WithBot ℕ∞ :=
  ⨆ X : ModuleCat.{u} R, projectiveDimension X

section RepresentationDimension

variable (k : Type u) (A : Type u) [Field k] [Ring A] [Algebra k A]

/-- `D(A_A) = Hom_k(A, k)`, the `k`-dual of the right regular module `A_A`. It is a left
`A`-module via `(a • f)(x) = f (x * a)`. -/
def DualRegular : Type u := A →ₗ[k] k

namespace DualRegular

instance : AddCommGroup (DualRegular k A) := inferInstanceAs (AddCommGroup (A →ₗ[k] k))

/-- View an element of `D(A)` as a `k`-linear map `A → k`. -/
def toLinearMap (f : DualRegular k A) : A →ₗ[k] k := f

/-- The left `A`-module structure on `D(A)`: `(a • f)(x) = f (x * a)`. -/
instance : Module A (DualRegular k A) where
  smul a f := (toLinearMap k A f).comp (LinearMap.mulRight k a)
  one_smul f := LinearMap.ext fun x => by
    change toLinearMap k A f (x * 1) = toLinearMap k A f x
    rw [mul_one]
  mul_smul a b f := LinearMap.ext fun x => by
    change toLinearMap k A f (x * (a * b)) = toLinearMap k A f (x * a * b)
    rw [mul_assoc]
  smul_zero a := LinearMap.ext fun x => rfl
  smul_add a f g := LinearMap.ext fun x => rfl
  add_smul a b f := LinearMap.ext fun x => by
    change toLinearMap k A f (x * (a + b)) =
      toLinearMap k A f (x * a) + toLinearMap k A f (x * b)
    rw [mul_add, map_add]
  zero_smul f := LinearMap.ext fun x => by
    change toLinearMap k A f (x * 0) = 0
    rw [mul_zero, map_zero]

end DualRegular

variable {A}

/-- `X ∈ add M`: `X` is a direct summand of a finite direct sum `M ^ n = M ⊕ ⋯ ⊕ M` of copies of
`M`, i.e. there are `A`-linear maps `i : X → M ^ n` and `r : M ^ n → X` with `r ∘ i = id`. -/
def IsSummandOfPower (X M : ModuleCat.{u} A) : Prop :=
  ∃ (n : ℕ) (i : X →ₗ[A] (Fin n → M)) (r : (Fin n → M) →ₗ[A] X), r ∘ₗ i = LinearMap.id

variable (A)

/-- `M` is a generator-cogenerator of `mod A`: it is finitely generated and both the regular module
`A` and its dual `D(A) = Hom_k(A, k)` are direct summands of finite direct sums of copies of `M`
(i.e. `A ⊕ D(A) ∈ add M`). -/
structure IsGeneratorCogenerator (M : ModuleCat.{u} A) : Prop where
  finite : Module.Finite A M
  generator : IsSummandOfPower (ModuleCat.of A A) M
  cogenerator : IsSummandOfPower (ModuleCat.of A (DualRegular k A)) M

/-- Auslander's representation dimension: the infimum, over all generator-cogenerators `M` of
`mod A`, of the global dimension of the endomorphism ring `End_A(M)`. -/
noncomputable def repdim : WithBot ℕ∞ :=
  ⨅ (M : ModuleCat.{u} A) (_ : IsGeneratorCogenerator k A M), globalDimension (Module.End A M)

end RepresentationDimension

/-! ## The two clauses of the conjecture -/

/-- Two rings are derived equivalent if their derived categories (Mathlib's `DerivedCategory` of the
module categories) are equivalent as triangulated categories. -/
def DerivedEquivalent (A B : Type u) [Ring A] [Ring B] : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} A)
  letI := HasDerivedCategory.standard (ModuleCat.{u} B)
  ∃ (e : DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (ModuleCat.{u} B))
    (_ : e.functor.CommShift ℤ), e.functor.IsTriangulated

/-- The canonical order embedding `WithBot ℕ∞ → EReal`: `⊥ ↦ ⊥`, `n ↦ n`, `⊤ ↦ ⊤`. It is used
only to compare values of `repdim` with real numbers. -/
noncomputable def toEReal (x : WithBot ℕ∞) : EReal :=
  WithBot.recBotCoe ⊥ (fun n : ℕ∞ => WithTop.recTopCoe ⊤ (fun m : ℕ => ((m : ℝ) : EReal)) n) x

/-- `v` is a realizable value of `repdim`: `v = repdim A` for some finite-dimensional algebra `A`
over some field `k`. -/
def IsRealizable (v : EReal) : Prop :=
  ∃ (k A : Type u) (_ : Field k) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A),
    toEReal (repdim k A) = v

/-- Clause (1): the realizable values of `repdim` are dense above `3`, i.e. dense in the half-line
`(3, ∞)` (Mathlib's `Dense`, in the subspace topology of `Set.Ioi (3 : ℝ) ⊆ ℝ`). -/
def DenseAbove3 : Prop :=
  Dense {x : Set.Ioi (3 : ℝ) | IsRealizable.{u} ((x : ℝ) : EReal)}

/-- Clause (2): the class of finite-dimensional algebras with `repdim = 3` is closed under derived
equivalence. -/
def ClosedUnderDerivedEquivalence : Prop :=
  ∀ (k A : Type u) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (k' B : Type u) [Field k'] [Ring B] [Algebra k' B] [FiniteDimensional k' B],
    repdim k A = 3 → DerivedEquivalent A B → repdim k' B = 3

/-! ## The proof -/

theorem toEReal_bot : toEReal ⊥ = ⊥ := rfl

theorem toEReal_top : toEReal ((⊤ : ℕ∞) : WithBot ℕ∞) = ⊤ := rfl

/-- Key lemma: an element of `WithBot ℕ∞` whose image in `EReal` is a real number `r` is a natural
number `m`, and `r = m`. -/
theorem exists_nat_of_toEReal_eq_coe (x : WithBot ℕ∞) (r : ℝ) (h : toEReal x = r) :
    ∃ m : ℕ, x = m ∧ r = m := by
  induction x with
  | bot => exact absurd h (by rw [toEReal_bot]; exact EReal.bot_ne_coe r)
  | coe n =>
    induction n with
    | top => exact absurd h (by rw [toEReal_top]; exact EReal.top_ne_coe r)
    | coe m =>
      refine ⟨m, rfl, ?_⟩
      have h' : ((m : ℝ) : EReal) = (r : EReal) := h
      exact (EReal.coe_eq_coe_iff.mp h').symm

/-- Step 1. Every finite (real) value of the representation dimension is a natural number:
`repdim k A ∈ WithBot ℕ∞` is an infimum of global dimensions, which are suprema of projective
dimensions. -/
theorem repdim_eq_nat_of_toEReal_eq (k A : Type u) [Field k] [Ring A] [Algebra k A] (r : ℝ)
    (h : toEReal (repdim k A) = r) : ∃ m : ℕ, repdim k A = m ∧ r = m :=
  exists_nat_of_toEReal_eq_coe _ r h

/-- Step 1, restated: every real realizable value of `repdim` is a natural number. -/
theorem eq_nat_of_isRealizable {r : ℝ} (h : IsRealizable.{u} (r : EReal)) : ∃ m : ℕ, r = m := by
  obtain ⟨k, A, _, _, _, _, hr⟩ := h
  obtain ⟨m, -, hm⟩ := repdim_eq_nat_of_toEReal_eq k A r hr
  exact ⟨m, hm⟩

/-- Step 2. No natural number lies strictly between `13/4` and `15/4`. -/
theorem no_nat_in_Ioo : ¬ ∃ m : ℕ, (13 / 4 : ℝ) < m ∧ (m : ℝ) < 15 / 4 := by
  rintro ⟨m, h1, h2⟩
  have h3 : (3 : ℝ) < m := by linarith
  have h4 : (m : ℝ) < 4 := by linarith
  have h3' : 3 < m := by exact_mod_cast h3
  have h4' : m < 4 := by exact_mod_cast h4
  omega

/-- Steps 1 and 2 combined: no realizable real value of `repdim` lies in `(13/4, 15/4)`. -/
theorem not_isRealizable_of_mem_Ioo {r : ℝ} (h1 : 13 / 4 < r) (h2 : r < 15 / 4) :
    ¬ IsRealizable.{u} (r : EReal) := by
  intro h
  obtain ⟨m, rfl⟩ := eq_nat_of_isRealizable h
  exact no_nat_in_Ioo ⟨m, h1, h2⟩

/-- **Clause (1) of the conjecture is false**: the nonempty open subset `(13/4, 15/4)` of the
half-line `(3, ∞)` contains no realizable value of `repdim`. -/
theorem not_denseAbove3 : ¬ DenseAbove3.{u} := by
  intro h
  have hU : IsOpen {x : Set.Ioi (3 : ℝ) | (x : ℝ) ∈ Set.Ioo (13 / 4 : ℝ) (15 / 4)} :=
    isOpen_Ioo.preimage continuous_subtype_val
  have hne : ({x : Set.Ioi (3 : ℝ) | (x : ℝ) ∈ Set.Ioo (13 / 4 : ℝ) (15 / 4)}).Nonempty :=
    ⟨⟨7 / 2, by norm_num⟩, by norm_num⟩
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := dense_iff_inter_open.mp h _ hU hne
  exact not_isRealizable_of_mem_Ioo hx1 hx2 hx

/-- **Conjecture 00000004042 is false, for every formalization of clause (2)**: whatever
proposition `P` expresses clause (2), the conjunction of clause (1) and `P` fails. -/
theorem conjecture_00000004042_false_of_any_clause2 (P : Prop) : ¬ (DenseAbove3.{u} ∧ P) :=
  fun h => not_denseAbove3 h.1

/-- **Conjecture 00000004042 is false.** The realizable values of `repdim` are not dense above `3`,
so the conjunction "dense above 3, and `{A | repdim A = 3}` closed under derived equivalence"
fails. -/
theorem conjecture_00000004042_false :
    ¬ (DenseAbove3.{u} ∧ ClosedUnderDerivedEquivalence.{u}) :=
  conjecture_00000004042_false_of_any_clause2 _

end Conjecture4042
