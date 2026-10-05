import Mathlib

/-!
# Conjecture 00000009984 (disproof)

Clause refuted: "each squared factor divides the dimension", read as: for every finite-dimensional
semisimple Hopf algebra `A` over `ℂ` and every irreducible (= simple) left `A`-module `M`,
`(dim_ℂ M)^2` divides `dim_ℂ A`.  The conjecture adds "the exception list is empty", so the clause
is asserted for every such `A`.

Counterexample: the group algebra `A = ℂ[S₃]` (`S₃ = Equiv.Perm (Fin 3)`, a symmetric group), with
Mathlib's Hopf algebra structure on `MonoidAlgebra`.  It is semisimple (Maschke), its comultiplication
makes every group element group-like (so its coalgebra is a direct sum of one-dimensional
subcoalgebras), and `dim_ℂ A = 6`.

Proof idea (no character table needed): if `(dim M)^2 ∣ 6` for every simple module `M`, then every
simple module is one-dimensional, so every element of `A` acts on it by a scalar, hence every
commutator `a*b - b*a` annihilates every simple submodule of `A`; since `A` is the sum of its simple
submodules, `a*b - b*a = 0`, i.e. `A` would be commutative.  But `ℂ[S₃]` is not commutative.
-/

open Module

namespace C9984

/-- The divisibility clause of the conjecture for a Hopf algebra `A` over `ℂ`: every simple
left `A`-module `M` that is finite-dimensional over `ℂ` (with the `ℂ`-structure being the
restriction of the `A`-structure) satisfies `(dim_ℂ M)^2 ∣ dim_ℂ A`. -/
def SquaredDimsDivide (A : Type) [Ring A] [HopfAlgebra ℂ A] : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M]
    [IsSimpleModule A M] [FiniteDimensional ℂ M], (finrank ℂ M) ^ 2 ∣ finrank ℂ A

/-- The symmetric group `S₃`. -/
abbrev S3 := Equiv.Perm (Fin 3)

/-- The group algebra `ℂ[S₃]`, with Mathlib's Hopf algebra structure. -/
abbrev H := MonoidAlgebra ℂ S3

instance : NeZero (Nat.card S3 : ℂ) :=
  ⟨by rw [Nat.card_eq_fintype_card, Fintype.card_perm]; norm_num⟩


/-- `ℂ[S₃]` is a semisimple ring (Maschke's theorem in Mathlib). -/
theorem H_semisimple : IsSemisimpleRing H := inferInstance

/-- `dim_ℂ ℂ[S₃] = 6`. -/
theorem finrank_H : finrank ℂ H = 6 := by
  rw [(MonoidAlgebra.coeffLinearEquiv ℂ).finrank_eq, Module.finrank_finsupp_self,
    Fintype.card_perm]; rfl

/-- Every group element is group-like: `Δ(g) = g ⊗ g`, `ε(g) = 1`, `S(g) = g⁻¹`. -/
theorem grouplike (g : S3) :
    Coalgebra.comul (R := ℂ) (MonoidAlgebra.single g (1 : ℂ) : H) =
        (MonoidAlgebra.single g 1 : H) ⊗ₜ[ℂ] (MonoidAlgebra.single g 1 : H) ∧
      Coalgebra.counit (R := ℂ) (MonoidAlgebra.single g (1 : ℂ) : H) = 1 ∧
      HopfAlgebra.antipode ℂ (MonoidAlgebra.single g (1 : ℂ) : H) = MonoidAlgebra.single g⁻¹ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [MonoidAlgebra.comul_single]
    simp
  · rw [MonoidAlgebra.counit_single]; simp
  · rw [MonoidAlgebra.antipode_single]; simp

/-- `ℂ[S₃]` is not commutative. -/
theorem H_not_comm :
    (MonoidAlgebra.single (Equiv.swap 0 1) 1 : H) * MonoidAlgebra.single (Equiv.swap 1 2) 1 ≠
      MonoidAlgebra.single (Equiv.swap 1 2) 1 * MonoidAlgebra.single (Equiv.swap 0 1) 1 := by
  rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single]
  rw [one_mul, Ne, MonoidAlgebra.single_left_inj (one_ne_zero (α := ℂ))]
  decide

/-- A positive natural number whose square divides `6` is `1`. -/
theorem sq_dvd_six {d : ℕ} (h : d ^ 2 ∣ 6) : d = 1 := by
  have h6 : d ^ 2 ≤ 6 := Nat.le_of_dvd (by norm_num) h
  have hd : d ≤ 2 := by nlinarith
  interval_cases d
  · simp at h
  · rfl
  · norm_num at h

/-- In a one-dimensional simple left ideal `N`, left multiplications commute. -/
theorem comm_on_simple (N : Submodule H H) [IsSimpleModule H N] (hN : finrank ℂ N = 1)
    (a b : H) : ∀ n ∈ N, (a * b - b * a) * n = 0 := by
  have := IsSimpleModule.nontrivial H N
  obtain ⟨v, hv⟩ := exists_ne (0 : N)
  have key : ∀ w : N, ∃ c : ℂ, c • v = w := (finrank_eq_one_iff_of_nonzero' v hv).mp hN
  obtain ⟨α, hα⟩ := key (a • v)
  obtain ⟨β, hβ⟩ := key (b • v)
  have hv' : (a * b - b * a) * (v : H) = 0 := by
    have ha : a * (v : H) = α • (v : H) := by
      have := congrArg Subtype.val hα; simpa using this.symm
    have hb : b * (v : H) = β • (v : H) := by
      have := congrArg Subtype.val hβ; simpa using this.symm
    rw [sub_mul, mul_assoc, mul_assoc, hb, ha, mul_smul_comm, mul_smul_comm, ha, hb, smul_smul,
      smul_smul, mul_comm, sub_self]
  intro n hn
  obtain ⟨c, hc⟩ := key ⟨n, hn⟩
  have : n = c • (v : H) := by have := congrArg Subtype.val hc; simpa using this.symm
  rw [this, mul_smul_comm, hv', smul_zero]

/-- `ℂ[S₃]` violates the divisibility clause. -/
theorem H_not_squaredDimsDivide : ¬ SquaredDimsDivide H := by
  intro h
  -- every simple left ideal is one-dimensional
  have dim1 : ∀ N : Submodule H H, IsSimpleModule H N → finrank ℂ N = 1 := by
    intro N hN
    exact sq_dvd_six (by simpa [finrank_H] using h N)
  -- hence every commutator annihilates `H`
  have hcomm : ∀ a b : H, a * b - b * a = 0 := by
    intro a b
    have hmem : a * b - b * a ∈ (⊤ : Submodule H H).annihilator := by
      rw [← IsSemisimpleModule.sSup_simples_eq_top H H, sSup_eq_iSup', Submodule.annihilator_iSup,
        Submodule.mem_iInf]
      rintro ⟨N, hN⟩
      rw [Submodule.mem_annihilator]
      intro n hn
      exact @comm_on_simple N hN (dim1 N hN) a b n hn
    simpa using (Submodule.mem_annihilator.mp hmem) 1 trivial
  exact H_not_comm (sub_eq_zero.mp (hcomm _ _))

/-- **Main theorem.** The conjecture's divisibility clause fails: not every finite-dimensional
semisimple Hopf algebra over `ℂ` has `(dim M)^2 ∣ dim A` for all its simple modules `M`. -/
theorem disproof :
    ¬ ∀ (A : Type) [Ring A] [HopfAlgebra ℂ A] [IsSemisimpleRing A] [FiniteDimensional ℂ A],
      SquaredDimsDivide A :=
  fun h => H_not_squaredDimsDivide (h H)

end C9984
