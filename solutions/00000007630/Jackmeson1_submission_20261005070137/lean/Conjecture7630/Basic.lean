import Mathlib

/-!
# Conjecture 00000007630

> Definition: Idempotent spectra and zero-divisor spectra are two layers. Conjecture: There exist
> two Clifford algebras with the same idempotent spectrum but different zero-divisor spectra, and
> the separation is realized by an explicit signature pair with the same idempotents but different
> zero divisors.

## Reading

* A Clifford algebra is Mathlib's `CliffordAlgebra Q` of a real quadratic form `Q`.
* The *idempotent spectrum* of an algebra `A` is its set of idempotents `{x | x * x = x}`;
  the *zero-divisor spectrum* is its set of zero divisors `{x | ∃ y ≠ 0, x * y = 0 ∨ y * x = 0}`.
* The *signature* of a real quadratic form is its Sylvester signature `(p, q, r)`
  (`p` positive, `q` negative, `r` null directions).

## The explicit signature pair (on `ℝ¹`)

* `Q₁(t) = -t²`, signature `(0, 1, 0)` (Mathlib's `CliffordAlgebraComplex.Q`); its Clifford
  algebra is `ℂ` (`CliffordAlgebraComplex.equiv`).
* `Q₀(t) = 0`, signature `(0, 0, 1)`; its Clifford algebra is the dual numbers `ℝ[ε]`
  (`CliffordAlgebraDualNumber.equiv`).

Both algebras have exactly the two trivial idempotents `0` and `1`. The first has no nonzero zero
divisor; in the second the generator `e = ι(1)` satisfies `e ≠ 0` and `e * e = 0`, and its zero
divisors are exactly the multiples `ι(r)` of the generator. In particular the two algebras are not
isomorphic.
-/

namespace Conjecture7630

open CliffordAlgebra TrivSqZeroExt

/-- Idempotent spectrum: the set of idempotents. -/
def idempotents (A : Type*) [Semiring A] : Set A := {x | IsIdempotentElem x}

/-- Zero-divisor spectrum: the set of (left or right) zero divisors. -/
def zeroDivisors (A : Type*) [Semiring A] : Set A := {x | ∃ y ≠ 0, x * y = 0 ∨ y * x = 0}

/-- `Q₁(t) = -t²`, signature `(0,1,0)`. -/
abbrev Q1 : QuadraticForm ℝ ℝ := CliffordAlgebraComplex.Q

/-- `Q₀(t) = 0`, signature `(0,0,1)`. -/
abbrev Q0 : QuadraticForm ℝ ℝ := 0

/-- `Cl(0,1,0) = CliffordAlgebra Q₁`. -/
abbrev Cl1 := CliffordAlgebra Q1

/-- `Cl(0,0,1) = CliffordAlgebra Q₀`. -/
abbrev Cl0 := CliffordAlgebra Q0

/-! ### Signatures -/

/-- `Q₁` is negative definite on `ℝ¹`: signature `(0,1,0)`. -/
theorem Q1_negDef : ∀ t : ℝ, t ≠ 0 → Q1 t < 0 := by
  intro t ht
  rw [CliffordAlgebraComplex.Q_apply]
  have := mul_self_pos.2 ht
  linarith

/-- `Q₀` vanishes identically: signature `(0,0,1)`. -/
theorem Q0_null : ∀ t : ℝ, Q0 t = 0 := fun _ => rfl

/-! ### `Cl(0,1,0) ≅ ℂ`: no zero divisors, trivial idempotents -/

instance : NoZeroDivisors Cl1 :=
  CliffordAlgebraComplex.equiv.injective.noZeroDivisors _ (map_zero _) (map_mul _)

theorem Cl1_zero_ne_one : (0 : Cl1) ≠ 1 := by
  intro h
  have := congrArg CliffordAlgebraComplex.equiv h
  simp at this

theorem idempotents_Cl1 : idempotents Cl1 = {0, 1} := by
  ext x
  simp [idempotents, IsIdempotentElem.iff_eq_zero_or_one]

theorem zeroDivisors_Cl1 : zeroDivisors Cl1 = {0} := by
  ext x
  simp only [zeroDivisors, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, h | h⟩
    · exact (mul_eq_zero.1 h).resolve_right hy
    · exact (mul_eq_zero.1 h).resolve_left hy
  · rintro rfl
    exact ⟨1, (Cl1_zero_ne_one).symm, Or.inl (zero_mul _)⟩

/-! ### `Cl(0,0,1) ≅ ℝ[ε]`: trivial idempotents, nonzero zero divisors -/

/-- Idempotents of the dual numbers are trivial. -/
theorem dual_idem (z : DualNumber ℝ) (hz : z * z = z) : z = 0 ∨ z = 1 := by
  have h1 := congrArg TrivSqZeroExt.fst hz
  have h2 := congrArg TrivSqZeroExt.snd hz
  simp only [fst_mul, snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op] at h1 h2
  have ha : z.fst = 0 ∨ z.fst = 1 := by
    have : z.fst * (z.fst - 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases ha with ha | ha
  · left
    rw [ha] at h2
    ext <;> simp_all
  · right
    rw [ha] at h2
    ext <;> simp_all

theorem Cl0_zero_ne_one : (0 : Cl0) ≠ 1 := by
  intro h
  have := congrArg (TrivSqZeroExt.fst ∘ CliffordAlgebraDualNumber.equiv) h
  simp at this

theorem idempotents_Cl0 : idempotents Cl0 = {0, 1} := by
  ext x
  simp only [idempotents, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    let e := (CliffordAlgebraDualNumber.equiv : Cl0 ≃ₐ[ℝ] DualNumber ℝ)
    have : e x * e x = e x := by rw [← map_mul, hx.eq]
    rcases dual_idem _ this with h | h
    · left; exact e.injective (by rw [h, map_zero])
    · right; exact e.injective (by rw [h, map_one])
  · rintro (rfl | rfl)
    · exact IsIdempotentElem.zero
    · exact IsIdempotentElem.one

/-- The generator `e = ι(1)` of `Cl(0,0,1)`. -/
noncomputable def gen : Cl0 := ι Q0 1

theorem gen_ne_zero : gen ≠ 0 := by
  intro h
  have := congrArg (TrivSqZeroExt.snd ∘ CliffordAlgebraDualNumber.equiv) h
  simp [gen] at this

theorem gen_mul_gen : gen * gen = 0 := CliffordAlgebraDualNumber.ι_mul_ι 1 1

theorem gen_mem_zeroDivisors : gen ∈ zeroDivisors Cl0 :=
  ⟨gen, gen_ne_zero, Or.inl gen_mul_gen⟩

/-- The zero divisors of `Cl(0,0,1)` are exactly the vectors `ι(r)`. -/
theorem zeroDivisors_Cl0 : zeroDivisors Cl0 = Set.range (ι Q0) := by
  let e := (CliffordAlgebraDualNumber.equiv : Cl0 ≃ₐ[ℝ] DualNumber ℝ)
  ext x
  simp only [zeroDivisors, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hfst : (e x).fst = 0 := by
      by_contra hne
      have hu : IsUnit (e x) := isUnit_iff_isUnit_fst.2 (Ne.isUnit hne)
      have hy' : e y ≠ 0 := fun h => hy (e.injective (by rw [h, map_zero]))
      rcases hxy with h | h
      · have : e x * e y = 0 := by rw [← map_mul, h, map_zero]
        exact hy' ((hu.mul_right_eq_zero).1 this)
      · have : e y * e x = 0 := by rw [← map_mul, h, map_zero]
        exact hy' ((hu.mul_left_eq_zero).1 this)
    refine ⟨(e x).snd, e.injective ?_⟩
    rw [CliffordAlgebraDualNumber.equiv_ι]
    ext <;> simp [hfst]
  · rintro ⟨r, rfl⟩
    exact ⟨gen, gen_ne_zero, Or.inl (CliffordAlgebraDualNumber.ι_mul_ι r 1)⟩

/-! ### The separation -/

/-- Isomorphic algebras have corresponding zero divisors, so `Cl(0,1,0) ≇ Cl(0,0,1)`. -/
theorem not_isomorphic : IsEmpty (Cl1 ≃ₐ[ℝ] Cl0) := by
  refine ⟨fun f => ?_⟩
  have hx : f.symm gen ∈ zeroDivisors Cl1 := by
    refine ⟨f.symm gen, fun h => gen_ne_zero ?_, Or.inl ?_⟩
    · simpa using congrArg f h
    · rw [← map_mul, gen_mul_gen, map_zero]
  rw [zeroDivisors_Cl1, Set.mem_singleton_iff] at hx
  exact gen_ne_zero (by simpa using congrArg f hx)

/-- **Main theorem.** The signature pair `(0,1,0)` (`Q₁ = -t²`) and `(0,0,1)` (`Q₀ = 0`) gives two
Clifford algebras with the same idempotent spectrum `{0, 1}` (exactly two idempotents in each) but
different zero-divisor spectra: `{0}` versus the line `ι(ℝ)`, which contains the nonzero element
`ι(1)` with `ι(1)² = 0`. -/
theorem separation :
    (∀ t : ℝ, t ≠ 0 → Q1 t < 0) ∧ (∀ t : ℝ, Q0 t = 0) ∧
    idempotents Cl1 = {0, 1} ∧ idempotents Cl0 = {0, 1} ∧
    (idempotents Cl1).ncard = 2 ∧ (idempotents Cl0).ncard = 2 ∧
    zeroDivisors Cl1 = {0} ∧ zeroDivisors Cl0 = Set.range (ι Q0) ∧
    (∃ x ∈ zeroDivisors Cl0, x ≠ 0 ∧ x * x = 0) ∧ (∀ x ∈ zeroDivisors Cl1, x = 0) ∧
    IsEmpty (Cl1 ≃ₐ[ℝ] Cl0) := by
  refine ⟨Q1_negDef, Q0_null, idempotents_Cl1, idempotents_Cl0, ?_, ?_, zeroDivisors_Cl1,
    zeroDivisors_Cl0, ⟨gen, gen_mem_zeroDivisors, gen_ne_zero, gen_mul_gen⟩, ?_,
    not_isomorphic⟩
  · rw [idempotents_Cl1]; exact Set.ncard_pair Cl1_zero_ne_one
  · rw [idempotents_Cl0]; exact Set.ncard_pair Cl0_zero_ne_one
  · intro x hx; rwa [zeroDivisors_Cl1, Set.mem_singleton_iff] at hx

end Conjecture7630
