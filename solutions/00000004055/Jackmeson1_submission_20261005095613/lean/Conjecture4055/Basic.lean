import Mathlib

/-!
# Conjecture 00000004055: no prime syzygy period over `k[x]/(x²)`

Conjecture text: "Definition: The syzygy Omega(M) is the kernel of the minimal projective
cover, and the period is the minimal number of iterations first returning to an isomorphic
module. Conjecture: On every self-injective algebra the syzygy period of any prescribed prime p
can be realized, and the minimal period 2 is attained by open-chain modules."

Counterexample: the dual numbers `A = k[ε]` (`ε² = 0`, isomorphic to `k[x]/(x²)`) over any
field `k`, Mathlib's `DualNumber k`, a 2-dimensional commutative algebra. It is self-injective
(Baer's criterion). If `π : P → M` is a projective cover (`P` projective, `π` onto, `ker π`
superfluous), then `ker π ⊆ εP`, so `ε` kills every syzygy. If `ε` kills `M`, then
`ker π = εP ≅ P/εP ≅ M`. Hence if `Ωⁿ(M) ≅ M` for some `n ≥ 1`, then `Ω(M) ≅ M`, so the period of
every periodic module is `1`, and no module has period `p` for any prime `p` (in particular `2`).
The simple module `εA` has period `1`, so the notion is not vacuous.

Syzygies are handled as a relation (`IsSyzygy R M N`: `N` is isomorphic to the kernel of some
projective cover of `M`), so no choice of cover is needed. We show that every syzygy of a
periodic module is isomorphic to it, so the result also holds when `Ω` is computed with any fixed
choice of projective covers. Modules are arbitrary (not necessarily finitely generated), which
only weakens the existence claim being refuted. Not formalized: the reading where `Ωⁿ(M) ≅ M` is
taken in the stable module category, and the undefined notion "open-chain module" (no module of
`k[ε]` has period `2` at all).
-/

open DualNumber TrivSqZeroExt

namespace C4055

universe u

/-! ## Definitions for an arbitrary ring -/

section Defs

variable {R P M : Type*} [Ring R] [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]

/-- A submodule `K ≤ P` is superfluous (small): `K ⊔ L = ⊤` forces `L = ⊤`. -/
def IsSuperfluous (K : Submodule R P) : Prop := ∀ L : Submodule R P, K ⊔ L = ⊤ → L = ⊤

/-- `π : P → M` is a (minimal) projective cover: `P` is projective, `π` is onto and `ker π` is
superfluous in `P`. -/
def IsProjectiveCover (π : P →ₗ[R] M) : Prop :=
  Module.Projective R P ∧ Function.Surjective π ∧ IsSuperfluous (LinearMap.ker π)

end Defs

/-- `N` is a syzygy `Ω(M)`: `N` is isomorphic to the kernel of a projective cover of `M`. -/
def IsSyzygy (R : Type) [Ring R] (M N : ModuleCat.{u} R) : Prop :=
  ∃ (P : ModuleCat.{u} R) (π : P →ₗ[R] M), IsProjectiveCover π ∧
    Nonempty (LinearMap.ker π ≃ₗ[R] N)

/-- `IterSyz R n M N`: `N ≅ Ωⁿ(M)` (`n` successive syzygies, starting from `M`). -/
def IterSyz (R : Type) [Ring R] : ℕ → ModuleCat.{u} R → ModuleCat.{u} R → Prop
  | 0, M, N => Nonempty (M ≃ₗ[R] N)
  | n + 1, M, N => ∃ M' : ModuleCat.{u} R, IsSyzygy R M M' ∧ IterSyz R n M' N

/-- `M` has syzygy period `p`: `p >= 1` is the least number of iterations with `Ω^p(M) ≅ M`. -/
def HasPeriod (R : Type) [Ring R] (M : ModuleCat.{u} R) (p : ℕ) : Prop :=
  0 < p ∧ IterSyz R p M M ∧ ∀ m, 0 < m → m < p → ¬ IterSyz R m M M

/-! ## The dual numbers -/

variable {k : Type} [Field k]

theorem eps_mul (x : k[ε]) : ε * x = inr x.fst := by ext <;> simp

theorem eq_eps_mul (x : k[ε]) (h : x.fst = 0) : x = ε * inl x.snd := by
  ext <;> simp [h]

theorem eps_smul_eps_smul {P : Type*} [AddCommGroup P] [Module k[ε] P] (q : P) :
    (ε : k[ε]) • (ε : k[ε]) • q = 0 := by rw [smul_smul, eps_mul_eps, zero_smul]

/-- `k[ε]` is finite-dimensional over `k`. -/
instance : Module.Finite k k[ε] := inferInstanceAs (Module.Finite k (k × k))

/-- `k[ε]` is self-injective, by Baer's criterion. -/
theorem selfInjective : Module.Injective k[ε] k[ε] := by
  refine Module.Baer.injective fun I g => ?_
  by_cases h1 : ∃ x ∈ I, x.fst ≠ 0
  · -- `I` contains a unit, so `I = ⊤`
    obtain ⟨x, hx, hx0⟩ := h1
    have hu : IsUnit x := isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hx0)
    have h1I : (1 : k[ε]) ∈ I := by
      obtain ⟨v, rfl⟩ := hu
      simpa using I.mul_mem_left (↑v⁻¹) hx
    refine ⟨LinearMap.toSpanSingleton k[ε] k[ε] (g ⟨1, h1I⟩), fun y hy => ?_⟩
    rw [LinearMap.toSpanSingleton_apply, ← map_smul]
    congr 1; exact Subtype.ext (by simp)
  · push Not at h1
    by_cases h2 : ∃ x ∈ I, x ≠ 0
    · obtain ⟨x, hx, hx0⟩ := h2
      have hxs : x.snd ≠ 0 := fun h => hx0 (by ext <;> simp [h1 x hx, h])
      set c := g ⟨x, hx⟩
      have hc : c.fst = 0 := by
        have : (ε : k[ε]) • (⟨x, hx⟩ : I) = 0 := by
          exact Subtype.ext (by simp [smul_eq_mul, eps_mul, h1 x hx])
        have h0 := congrArg g this
        rw [map_smul, map_zero, smul_eq_mul, eps_mul] at h0
        simpa using congrArg TrivSqZeroExt.snd h0
      refine ⟨LinearMap.toSpanSingleton k[ε] k[ε] (inl (c.snd / x.snd)), fun y hy => ?_⟩
      have hyx : (⟨y, hy⟩ : I) = (inl (y.snd / x.snd) : k[ε]) • ⟨x, hx⟩ := by
        ext <;> simp [smul_eq_mul, h1 y hy, h1 x hx, hxs]
      rw [hyx, map_smul, LinearMap.toSpanSingleton_apply, smul_eq_mul, smul_eq_mul]
      ext <;> simp [h1 y hy, hc, c]
      field_simp
    · push Not at h2
      refine ⟨0, fun y hy => ?_⟩
      have : (⟨y, hy⟩ : I) = 0 := Subtype.ext (h2 y hy)
      rw [this, map_zero, LinearMap.zero_apply]

section Cover

variable {P M : Type*} [AddCommGroup P] [Module k[ε] P] [AddCommGroup M] [Module k[ε] M]

/-- In a projective module with splitting `s`, an element whose coordinates all lie in `εA`
lies in `εP`. -/
theorem exists_eps_smul (s : P →ₗ[k[ε]] P →₀ k[ε])
    (hs : Finsupp.linearCombination k[ε] id ∘ₗ s = .id) (p : P) (h : ∀ i, (s p i).fst = 0) :
    ∃ q, p = (ε : k[ε]) • q := by
  refine ⟨Finsupp.linearCombination k[ε] id
    (Finsupp.mapRange (fun c : k[ε] => (inl c.snd : k[ε])) (by rw [snd_zero, inl_zero]) (s p)), ?_⟩
  have hp : Finsupp.linearCombination k[ε] id (s p) = p := LinearMap.congr_fun hs p
  rw [← map_smul]
  conv_lhs => rw [← hp]
  congr 1
  ext i : 1
  rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact eq_eps_mul _ (h i)

/-- In a projective module, `εp = 0` implies `p ∈ εP`. -/
theorem mem_eps_of_eps_smul [Module.Projective k[ε] P] (p : P) (hp : (ε : k[ε]) • p = 0) :
    ∃ q, p = (ε : k[ε]) • q := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹_›
  refine exists_eps_smul s hs p fun i => ?_
  have h := congrArg (fun f => f i) (map_smul s (ε : k[ε]) p)
  simp only [hp, map_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, smul_eq_mul,
    eps_mul] at h
  simpa using (congrArg TrivSqZeroExt.snd h).symm

/-- A superfluous submodule of a projective module lies in `εP`. -/
theorem superfluous_le_eps [Module.Projective k[ε] P] (K : Submodule k[ε] P)
    (hK : IsSuperfluous K) (y : P) (hy : y ∈ K) : ∃ q, y = (ε : k[ε]) • q := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹_›
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, (s y i).fst ≠ 0 := by
    by_contra h; push Not at h; exact hne (exists_eps_smul s hs y h)
  let φ : P →ₗ[k[ε]] k[ε] := Finsupp.lapply i ∘ₗ s
  let L : Submodule k[ε] P :=
    { carrier := {p | (φ p).fst = 0}
      add_mem' := fun ha hb => by simp_all
      zero_mem' := by simp
      smul_mem' := fun c p hp => by simp_all [smul_eq_mul] }
  have hφ : ∀ p, φ p = s p i := fun p => rfl
  have hL : L ≠ ⊤ := fun h => hi (by
    have : y ∈ L := h ▸ Submodule.mem_top
    simpa [L, hφ] using this)
  refine hL (hK L (eq_top_iff.mpr fun p _ => ?_))
  set c : k[ε] := inl ((s p i).fst / (s y i).fst)
  have hdec : p = c • y + (p - c • y) := by abel
  rw [hdec]
  refine Submodule.add_mem_sup (K.smul_mem _ hy) ?_
  show (φ (p - c • y)).fst = 0
  rw [map_sub, map_smul, hφ, hφ, smul_eq_mul, fst_sub, fst_mul, fst_inl,
    div_mul_cancel₀ _ hi, sub_self]

/-- Every element of the kernel of a projective cover is killed by `ε`. -/
theorem eps_smul_ker {π : P →ₗ[k[ε]] M} (hπ : IsProjectiveCover π) (y : P)
    (hy : y ∈ LinearMap.ker π) : (ε : k[ε]) • y = 0 := by
  have := hπ.1
  obtain ⟨q, rfl⟩ := superfluous_le_eps _ hπ.2.2 y hy
  exact eps_smul_eps_smul q

/-- If `ε` kills `M`, the kernel of any projective cover of `M` is isomorphic to `M`. -/
theorem ker_equiv_of_eps {π : P →ₗ[k[ε]] M} (hπ : IsProjectiveCover π)
    (hM : ∀ m : M, (ε : k[ε]) • m = 0) : Nonempty (LinearMap.ker π ≃ₗ[k[ε]] M) := by
  have := hπ.1
  let μ : P →ₗ[k[ε]] LinearMap.ker π :=
    LinearMap.codRestrict (LinearMap.ker π) ((ε : k[ε]) • LinearMap.id)
      fun p => by simp [hM]
  have hμ : Function.Surjective μ := by
    rintro ⟨y, hy⟩
    obtain ⟨q, rfl⟩ := superfluous_le_eps _ hπ.2.2 y hy
    exact ⟨q, rfl⟩
  have hker : LinearMap.ker μ = LinearMap.ker π := by
    ext p
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      have h' : (ε : k[ε]) • p = 0 := congrArg Subtype.val h
      obtain ⟨q, rfl⟩ := mem_eps_of_eps_smul p h'
      rw [map_smul, hM]
    · intro h
      exact Subtype.ext (eps_smul_ker hπ p h)
  exact ⟨(LinearMap.quotKerEquivOfSurjective μ hμ).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ LinearMap.quotKerEquivOfSurjective π hπ.2.1⟩

end Cover

/-! ## Periods over `k[ε]` -/

theorem killed_of_equiv {M N : Type*} [AddCommGroup M] [Module k[ε] M] [AddCommGroup N]
    [Module k[ε] N] (e : M ≃ₗ[k[ε]] N) (hM : ∀ m : M, (ε : k[ε]) • m = 0) (n : N) :
    (ε : k[ε]) • n = 0 := by
  rw [← e.apply_symm_apply n, ← map_smul, hM, map_zero]

/-- Every syzygy is killed by `ε` (is semisimple). -/
theorem syzygy_killed {M N : ModuleCat.{u} k[ε]} (h : IsSyzygy k[ε] M N) (n : N) :
    (ε : k[ε]) • n = 0 := by
  obtain ⟨P, π, hπ, ⟨e⟩⟩ := h
  exact killed_of_equiv e (fun y => Subtype.ext (eps_smul_ker hπ y.1 y.2)) n

/-- If `ε` kills `M`, every syzygy of `M` is isomorphic to `M`. -/
theorem syzygy_equiv {M N : ModuleCat.{u} k[ε]} (hM : ∀ m : M, (ε : k[ε]) • m = 0)
    (h : IsSyzygy k[ε] M N) : Nonempty (N ≃ₗ[k[ε]] M) := by
  obtain ⟨P, π, hπ, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := ker_equiv_of_eps hπ hM
  exact ⟨e.symm ≪≫ₗ f⟩

theorem iterSyz_killed : ∀ (n : ℕ) (M N : ModuleCat.{u} k[ε]), IterSyz k[ε] (n + 1) M N →
    ∀ x : N, (ε : k[ε]) • x = 0
  | 0, _, _, ⟨_, h, ⟨e⟩⟩ => killed_of_equiv e (syzygy_killed h)
  | n + 1, _, N, ⟨M', _, h⟩ => iterSyz_killed n M' N h

/-- If `Ωⁿ(M) ≅ M` for some `n >= 1`, then every syzygy of `M` is isomorphic to `M`, and
`Ω(M) ≅ M`. -/
theorem periodic_imp_period_one (M : ModuleCat.{u} k[ε]) (n : ℕ) (hn : 0 < n)
    (h : IterSyz k[ε] n M M) :
    (∀ N, IsSyzygy k[ε] M N → Nonempty (N ≃ₗ[k[ε]] M)) ∧ IterSyz k[ε] 1 M M := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hM := iterSyz_killed m M M h
  refine ⟨fun N hN => syzygy_equiv hM hN, ?_⟩
  obtain ⟨M', hM', -⟩ := h
  obtain ⟨e⟩ := syzygy_equiv hM hM'
  exact ⟨M', hM', ⟨e⟩⟩

/-- Every module over `k[ε]` that has a syzygy period has period `1`. -/
theorem period_eq_one (M : ModuleCat.{u} k[ε]) (p : ℕ) (h : HasPeriod k[ε] M p) : p = 1 := by
  obtain ⟨hp, hM, hmin⟩ := h
  by_contra hne
  exact hmin 1 one_pos (by omega) (periodic_imp_period_one M p hp hM).2

/-- No module over `k[ε]` has a prime syzygy period (in particular, none has period `2`). -/
theorem no_prime_period (M : ModuleCat.{u} k[ε]) (p : ℕ) (hp : p.Prime) :
    ¬ HasPeriod k[ε] M p := fun h => hp.one_lt.ne' (period_eq_one M p h)

/-- Non-vacuity: the simple module `εA` (the range of multiplication by `ε`) has period `1`. -/
theorem simple_has_period_one :
    HasPeriod k[ε] (ModuleCat.of k[ε] (LinearMap.range (LinearMap.mulLeft k[ε] (ε : k[ε])))) 1 := by
  set π := LinearMap.mulLeft k[ε] (ε : k[ε])
  have hkr : LinearMap.ker π = LinearMap.range π := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, π, LinearMap.mulLeft_apply]
    constructor
    · intro h
      have hx : x.fst = 0 := by simpa [eps_mul] using congrArg TrivSqZeroExt.snd h
      exact ⟨inl x.snd, (eq_eps_mul x hx).symm⟩
    · rintro ⟨y, rfl⟩
      rw [← mul_assoc, eps_mul_eps, zero_mul]
  have hker : LinearMap.ker π.rangeRestrict = LinearMap.ker π := LinearMap.ker_rangeRestrict π
  refine ⟨one_pos, ⟨_, ⟨ModuleCat.of k[ε] k[ε], π.rangeRestrict, ⟨inferInstance,
    LinearMap.surjective_rangeRestrict π, ?_⟩, ⟨LinearEquiv.ofEq _ _ (hker.trans hkr)⟩⟩,
    ⟨LinearEquiv.refl _ _⟩⟩, fun m h1 h2 => by omega⟩
  intro L hL
  have h1 : (1 : k[ε]) ∈ LinearMap.ker π ⊔ L := hker ▸ hL ▸ Submodule.mem_top
  obtain ⟨a, ha, l, hl, hal⟩ := Submodule.mem_sup.mp h1
  have ha0 : a.fst = 0 := by
    simpa [π, eps_mul] using congrArg TrivSqZeroExt.snd (LinearMap.mem_ker.mp ha)
  have hu : IsUnit l := isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr (by
    have := congrArg TrivSqZeroExt.fst hal
    simp only [fst_add, fst_one, ha0, zero_add] at this
    simp [this]))
  exact Ideal.eq_top_of_isUnit_mem L hl hu

/-- Over `k[ε]` the least syzygy period of any module is `1` (attained by `εA`), and no module
has period `2`. -/
theorem minimal_period_is_one :
    (∃ M : ModuleCat.{0} k[ε], HasPeriod k[ε] M 1) ∧
      ∀ M : ModuleCat.{u} k[ε], ¬ HasPeriod k[ε] M 2 :=
  ⟨⟨_, simple_has_period_one⟩, fun M => no_prime_period M 2 Nat.prime_two⟩

/-! ## The conjecture -/

/-- The first clause of the conjecture, for commutative finite-dimensional algebras over `k`
(where left and right self-injectivity coincide): every such self-injective algebra has, for
every prime `p`, a module of syzygy period `p`. The clause for all self-injective algebras
implies this one. -/
def PrimePeriodsRealized (k : Type) [Field k] : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra k R], Module.Finite k R → Module.Injective R R →
    ∀ p : ℕ, p.Prime → ∃ M : ModuleCat.{0} R, HasPeriod R M p

/-- The period-2 clause, read as: every such algebra has a module of syzygy period `2`. -/
def PeriodTwoRealized (k : Type) [Field k] : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra k R], Module.Finite k R → Module.Injective R R →
    ∃ M : ModuleCat.{0} R, HasPeriod R M 2

/-- Main theorem: for every field `k`, the first clause fails (witness `k[ε]`). -/
theorem conjecture_4055_false (k : Type) [Field k] : ¬ PrimePeriodsRealized k := fun h => by
  obtain ⟨M, hM⟩ := h k[ε] inferInstance selfInjective 2 Nat.prime_two
  exact no_prime_period M 2 Nat.prime_two hM

/-- The period-2 clause also fails for every field `k` (witness `k[ε]`). -/
theorem period_two_false (k : Type) [Field k] : ¬ PeriodTwoRealized k := fun h => by
  obtain ⟨M, hM⟩ := h k[ε] inferInstance selfInjective
  exact no_prime_period M 2 Nat.prime_two hM

end C4055
