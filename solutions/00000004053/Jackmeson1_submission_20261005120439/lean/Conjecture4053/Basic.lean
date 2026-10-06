import Mathlib

/-!
# Conjecture 00000004053: a periodic module whose period has a prime factor `2 ∤ |D|`

Conjecture text: "Definition: A periodic module is one with Omega^n M isomorphic to M.
Conjecture: The prime factors of the minimal period of a periodic module always divide prime
factors of the order of the defect group, and every power of every admissible prime is realized in
some explicit block."

Counterexample to the first clause: `p = 3`, `G = C₃` (Mathlib's `Multiplicative (ZMod 3)`),
`A = F₃[C₃]` (Mathlib's group algebra `MonoidAlgebra (ZMod 3) G`), and the trivial module
`k = F₃` (every group element acts as the identity). With `t = g - 1` we prove `t³ = 0`, `t² ≠ 0`
and `ker ε = tA` for the augmentation `ε`, so `A` behaves as `F₃[t]/(t³)`. For a cyclic module
`M = A m₀` with `m₀ ∉ tM`, every projective cover `π : P → M` has `P ≅ A` and
`ker π ≅ ann(m₀)` (proved for arbitrary projective `P`, not only for a chosen cover). Hence
`Ωk ≅ N1 = ker ε = (t)`, `Ω²k ≅ N2 = ann(t) = (t²) ≅ k`, and `Ωk ≇ k` since `t` kills `k` but not
`(t)`. So the minimal period of `k` is `2`. Every subgroup `D ≤ C₃` has order `1` or `3`, so `2`
divides no prime factor of `|D|` (nor `|D|` itself). The defect group of a block of `F₃[G]` is a
subgroup of `G`, so the first clause fails whichever block/defect group is meant.

Syzygies are a relation (`IsSyzygy R M N`: `N` is isomorphic to the kernel of some projective
cover of `M`), as in the accepted package for 00000004055; we also show that every second syzygy
of `k` is isomorphic to `k`, so the period does not depend on the choice of covers. The second
clause ("admissible prime", "explicit block") is not formalized; the conjunction fails because the
first clause fails.
-/

open MonoidAlgebra

namespace C4053

/-! ## Projective covers and syzygies -/

section Defs

variable {R P M : Type*} [Ring R] [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]

/-- A submodule `K ≤ P` is superfluous (small): `K ⊔ L = ⊤` forces `L = ⊤`. -/
def IsSuperfluous (K : Submodule R P) : Prop := ∀ L : Submodule R P, K ⊔ L = ⊤ → L = ⊤

/-- `π : P → M` is a projective cover: `P` is projective, `π` is onto and `ker π` is
superfluous. -/
def IsProjectiveCover (π : P →ₗ[R] M) : Prop :=
  Module.Projective R P ∧ Function.Surjective π ∧ IsSuperfluous (LinearMap.ker π)

end Defs

/-- `M` is indecomposable: nonzero, and not the direct sum of two nonzero submodules. -/
def IsIndecomposable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  Nontrivial M ∧ ∀ S T : Submodule R M, IsCompl S T → S = ⊥ ∨ T = ⊥

/-- `N` is a syzygy `Ω(M)`: `N` is isomorphic to the kernel of a projective cover of `M`. -/
def IsSyzygy (R : Type) [Ring R] (M N : ModuleCat.{0} R) : Prop :=
  ∃ (P : ModuleCat.{0} R) (π : P →ₗ[R] M), IsProjectiveCover π ∧
    Nonempty (LinearMap.ker π ≃ₗ[R] N)

/-- `IterSyz R n M N`: `N ≅ Ωⁿ(M)` (`n` successive syzygies, starting from `M`). -/
def IterSyz (R : Type) [Ring R] : ℕ → ModuleCat.{0} R → ModuleCat.{0} R → Prop
  | 0, M, N => Nonempty (M ≃ₗ[R] N)
  | n + 1, M, N => ∃ M' : ModuleCat.{0} R, IsSyzygy R M M' ∧ IterSyz R n M' N

/-- `M` has minimal syzygy period `p`: `p ≥ 1` is the least `n ≥ 1` with `Ωⁿ(M) ≅ M`. -/
def HasPeriod (R : Type) [Ring R] (M : ModuleCat.{0} R) (p : ℕ) : Prop :=
  0 < p ∧ IterSyz R p M M ∧ ∀ m, 0 < m → m < p → ¬ IterSyz R m M M

/-! ## The group algebra -/

/-- The cyclic group `C₃` of order 3. -/
abbrev G := Multiplicative (ZMod 3)
/-- The group algebra `A = F₃[C₃]`. -/
abbrev A := MonoidAlgebra (ZMod 3) G
/-- A generator `g` of `C₃`. -/
def g : G := Multiplicative.ofAdd 1
/-- `t = g - 1 ∈ A`. -/
noncomputable def t : A := MonoidAlgebra.of (ZMod 3) G g - 1
/-- The augmentation `ε : A → F₃`, `ε(h) = 1` for every `h ∈ G`. -/
noncomputable def ε : A →ₐ[ZMod 3] ZMod 3 := MonoidAlgebra.lift (ZMod 3) (ZMod 3) G 1

local notation "ι" => algebraMap (ZMod 3) A

theorem eps_of (h : G) : ε (MonoidAlgebra.of (ZMod 3) G h) = 1 := by simp [ε]

theorem eps_t : ε t = 0 := by rw [t, map_sub, eps_of, map_one, sub_self]

theorem g_pow : ∀ m : G, m = g ^ (Multiplicative.toAdd m).val := by decide

theorem three_eq_zero : (3 : A) = 0 := by
  rw [← map_ofNat ι 3, show (OfNat.ofNat 3 : ZMod 3) = 0 from rfl, map_zero]

theorem t_cube : t ^ 3 = 0 := by
  have hg : (MonoidAlgebra.of (ZMod 3) G g) ^ 3 = 1 := by
    rw [← map_pow, show g ^ 3 = 1 from by decide, map_one]
  unfold t
  linear_combination hg + (MonoidAlgebra.of (ZMod 3) G g - MonoidAlgebra.of (ZMod 3) G g ^ 2) *
    three_eq_zero

theorem t_sq_ne_zero : t ^ 2 ≠ 0 := by
  have ht : t ^ 2 = MonoidAlgebra.of (ZMod 3) G (g ^ 2) + MonoidAlgebra.of (ZMod 3) G g + 1 := by
    rw [map_pow]; unfold t
    linear_combination (-(MonoidAlgebra.of (ZMod 3) G g)) * three_eq_zero
  intro h
  have := congrArg (fun x : A => x.coeff 1) (ht.symm.trans h)
  have h1 : (g ^ 2 : G) ≠ 1 := by decide
  have h2 : g ≠ 1 := by decide
  simp [MonoidAlgebra.coeff_add, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, h1, h2] at this

/-- `ker ε = tA`, in the form `a = ε(a) + t d`. -/
theorem exists_t_mul (a : A) : ∃ d, a = ι (ε a) + t * d := by
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    obtain ⟨d, hd⟩ := sub_one_dvd_pow_sub_one (MonoidAlgebra.of (ZMod 3) G g)
      (Multiplicative.toAdd m).val
    have hm : MonoidAlgebra.of (ZMod 3) G m =
        MonoidAlgebra.of (ZMod 3) G g ^ (Multiplicative.toAdd m).val := by
      rw [← map_pow, ← g_pow]
    refine ⟨d, ?_⟩
    rw [eps_of, map_one]; unfold t
    linear_combination hm + hd
  | add x y hx hy =>
    obtain ⟨⟨d1, h1⟩, ⟨d2, h2⟩⟩ := And.intro hx hy
    exact ⟨d1 + d2, by rw [map_add, map_add]; linear_combination h1 + h2⟩
  | smul r x hx =>
    obtain ⟨d, hd⟩ := hx
    refine ⟨ι r * d, ?_⟩
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_mul]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    linear_combination (ι r) * hd

theorem ker_eps {a : A} (h : ε a = 0) : ∃ d, a = t * d := by
  obtain ⟨d, hd⟩ := exists_t_mul a
  exact ⟨d, by rw [hd, h, map_zero, zero_add]⟩

theorem t_sq_mul (c : A) : t ^ 2 * c = ι (ε c) * t ^ 2 := by
  obtain ⟨d, hd⟩ := exists_t_mul c
  linear_combination (t ^ 2) * hd + d * t_cube

theorem inv_smul_t_sq {x : ZMod 3} (hx : x ≠ 0) : t ^ 2 = ι x⁻¹ * (ι x * t ^ 2) := by
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]

theorem eq_zero_of_smul_t_sq {x : ZMod 3} (h : ι x * t ^ 2 = 0) : x = 0 := by
  by_contra hx
  exact t_sq_ne_zero (by rw [inv_smul_t_sq hx, h, mul_zero])

theorem eps_of_t_sq_mul {c : A} (h : t ^ 2 * c = 0) : ε c = 0 :=
  eq_zero_of_smul_t_sq (by rw [← t_sq_mul, h])

/-- `t²` lies in every nonzero principal ideal of `A`. -/
theorem t_sq_mem (a : A) (ha : a ≠ 0) : ∃ b, t ^ 2 = b * a := by
  by_cases h0 : ε a = 0
  · obtain ⟨d, rfl⟩ := ker_eps h0
    by_cases h1 : ε d = 0
    · obtain ⟨d', rfl⟩ := ker_eps h1
      have he : ε d' ≠ 0 := fun h =>
        ha (by rw [← mul_assoc, ← sq, t_sq_mul, h, map_zero, zero_mul])
      exact ⟨ι (ε d')⁻¹, (inv_smul_t_sq he).trans (by rw [← t_sq_mul d']; ring)⟩
    · exact ⟨ι (ε d)⁻¹ * t, (inv_smul_t_sq h1).trans (by rw [← t_sq_mul d]; ring)⟩
  · exact ⟨ι (ε a)⁻¹ * t ^ 2, (inv_smul_t_sq h0).trans (by rw [← t_sq_mul a]; ring)⟩

/-- A submodule of `A` inside `ker ε` is superfluous. -/
theorem superfluous_of_le_ker (K : Submodule A A) (hK : ∀ x ∈ K, ε x = 0) :
    IsSuperfluous K := fun L hL => by
  obtain ⟨x, hx, l, hl, hxl⟩ := Submodule.mem_sup.mp (hL ▸ Submodule.mem_top : (1 : A) ∈ K ⊔ L)
  have hel : ε (l - 1) = 0 := by
    have := congrArg ε hxl
    rw [map_add, hK x hx, zero_add, map_one] at this
    rw [map_sub, this, map_one, sub_self]
  obtain ⟨d, hd⟩ := ker_eps hel
  have h1L : (1 - t * d + t ^ 2 * d ^ 2) * l = 1 := by
    linear_combination (1 - t * d + t ^ 2 * d ^ 2) * hd + d ^ 3 * t_cube
  exact (Ideal.eq_top_iff_one L).mpr (h1L ▸ L.smul_mem _ hl)

/-- In a projective `A`-module, `t² p = 0` implies `p ∈ tP`. -/
theorem mem_t_of_t_sq_smul {P : Type*} [AddCommGroup P] [Module A P] [Module.Projective A P]
    (p : P) (hp : t ^ 2 • p = 0) : ∃ q, p = t • q := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹_›
  have hex : ∀ c : A, ∃ d, ε c = 0 → c = t * d := fun c => by
    by_cases h : ε c = 0
    · exact (ker_eps h).imp fun d hd _ => hd
    · exact ⟨0, fun h' => absurd h' h⟩
  choose f hf using hex
  have hc : ∀ i, ε (s p i) = 0 := fun i => by
    apply eps_of_t_sq_mul
    have := congrArg (fun F => F i) (map_smul s (t ^ 2) p)
    simpa [hp] using this.symm
  refine ⟨(s p).sum fun i c => f c • i, ?_⟩
  have hp' : Finsupp.linearCombination A id (s p) = p := LinearMap.congr_fun hs p
  conv_lhs => rw [← hp']
  rw [Finsupp.linearCombination_apply, Finsupp.smul_sum]
  exact Finsupp.sum_congr fun i _ => by rw [smul_smul, ← hf _ (hc i)]; rfl

/-! ## Cyclic modules: projective covers and their kernels -/

section Cyclic

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- `m₀` generates `M` and `m₀ ∉ tM`. -/
def CyclicGen (m₀ : M) : Prop := (∀ m : M, ∃ a : A, m = a • m₀) ∧ ∀ m : M, m₀ ≠ t • m

theorem CyclicGen.map {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) {m₀ : M}
    (h : CyclicGen m₀) : CyclicGen (e m₀) :=
  ⟨fun n => (h.1 (e.symm n)).imp fun a ha => by rw [← e.map_smul, ← ha, e.apply_symm_apply],
   fun n hn => h.2 (e.symm n) (by rw [← e.symm.map_smul, ← hn, e.symm_apply_apply])⟩

theorem ker_toSpan_map {N : Type*} [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (m₀ : M) :
    LinearMap.ker (LinearMap.toSpanSingleton A N (e m₀)) =
      LinearMap.ker (LinearMap.toSpanSingleton A M m₀) := by
  ext a
  simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← e.map_smul,
    LinearEquiv.map_eq_zero_iff]

theorem eps_of_smul_gen {m₀ : M} (hm : CyclicGen m₀) (a : A) (ha : a • m₀ = 0) : ε a = 0 := by
  by_contra h
  obtain ⟨d, hd⟩ := exists_t_mul a
  have hinv : ι (ε a)⁻¹ * ι (ε a) = 1 := by rw [← map_mul, inv_mul_cancel₀ h, map_one]
  apply hm.2 (-(ι (ε a)⁻¹ * d) • m₀)
  rw [smul_smul, show t * -(ι (ε a)⁻¹ * d) = 1 - ι (ε a)⁻¹ * a by
    linear_combination (ι (ε a)⁻¹) * hd + hinv, sub_smul, one_smul, mul_smul, ha, smul_zero,
    sub_zero]

/-- Existence: `a ↦ a • m₀` is a projective cover. -/
theorem toSpan_isCover {m₀ : M} (hm : CyclicGen m₀) :
    IsProjectiveCover (LinearMap.toSpanSingleton A M m₀) :=
  ⟨inferInstance, fun m => (hm.1 m).imp fun a ha => by simp [ha],
    superfluous_of_le_ker _ fun a ha => eps_of_smul_gen hm a (by simpa using ha)⟩

/-- Uniqueness: the kernel of every projective cover of `M` is isomorphic to the annihilator
of `m₀`. -/
theorem ker_cover_equiv {P : Type*} [AddCommGroup P] [Module A P] {m₀ : M} (hm : CyclicGen m₀)
    {π : P →ₗ[A] M} (hπ : IsProjectiveCover π) :
    Nonempty (LinearMap.ker π ≃ₗ[A] LinearMap.ker (LinearMap.toSpanSingleton A M m₀)) := by
  obtain ⟨hP, hsurj, hsup⟩ := hπ
  obtain ⟨p₀, hp₀⟩ := hsurj m₀
  set φ := LinearMap.toSpanSingleton A P p₀ with hφ
  have hφs : Function.Surjective φ := by
    refine LinearMap.range_eq_top.mp (hsup _ (eq_top_iff.mpr fun p _ => ?_))
    obtain ⟨a, ha⟩ := hm.1 (π p)
    rw [show p = (p - a • p₀) + a • p₀ by abel]
    refine Submodule.add_mem_sup ?_ ⟨a, by simp [φ]⟩
    rw [LinearMap.mem_ker, map_sub, map_smul, hp₀, ha, sub_self]
  have hφi : Function.Injective φ := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun a ha => by_contra fun hne => ?_)
    obtain ⟨b, hb⟩ := t_sq_mem a hne
    obtain ⟨q, hq⟩ := mem_t_of_t_sq_smul p₀ (by
      rw [hb, mul_smul]; simp only [φ, LinearMap.toSpanSingleton_apply] at ha; rw [ha, smul_zero])
    exact hm.2 (π q) (by rw [← hp₀, hq, map_smul])
  let e := LinearEquiv.ofBijective φ ⟨hφi, hφs⟩
  have hcomp : π ∘ₗ (e : A →ₗ[A] P) = LinearMap.toSpanSingleton A M m₀ := by
    ext; show π ((1 : A) • p₀) = (1 : A) • m₀; rw [one_smul, one_smul, hp₀]
  refine ⟨LinearEquiv.ofSubmodules e.symm _ _ ?_⟩
  rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm, ← hcomp, LinearMap.ker_comp]

end Cyclic

/-! ## The trivial module and its syzygies -/

/-- The trivial module `k = F₃` (as a type synonym). -/
def Triv : Type := ZMod 3

instance : AddCommGroup Triv := inferInstanceAs (AddCommGroup (ZMod 3))
instance : Module (ZMod 3) Triv := inferInstanceAs (Module (ZMod 3) (ZMod 3))
instance : Finite Triv := inferInstanceAs (Finite (ZMod 3))
/-- `a • x = ε(a) x`: every group element acts as the identity. -/
noncomputable instance : Module A Triv := Module.compHom Triv (ε : A →+* ZMod 3)

def Triv.mk (x : ZMod 3) : Triv := x
def Triv.val (x : Triv) : ZMod 3 := x

theorem triv_smul (a : A) (x : Triv) : a • x = Triv.mk (ε a * x.val) := rfl

theorem triv_group_acts_trivially (h : G) (x : Triv) :
    MonoidAlgebra.of (ZMod 3) G h • x = x := by
  rw [triv_smul, eps_of, one_mul]; rfl

theorem t_smul_triv (x : Triv) : t • x = 0 := by
  rw [triv_smul, eps_t, zero_mul]; rfl

theorem cyc_triv : CyclicGen (Triv.mk 1) := by
  refine ⟨fun m => ⟨ι m.val, ?_⟩, fun m h => ?_⟩
  · rw [triv_smul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    exact (mul_one m.val).symm
  · exact one_ne_zero (α := ZMod 3) (h.trans (t_smul_triv m))

/-- `k` is simple. -/
theorem triv_simple (S : Submodule A Triv) : S = ⊥ ∨ S = ⊤ := by
  refine or_iff_not_imp_left.mpr fun h => eq_top_iff.mpr fun y _ => ?_
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hx0' : x.val ≠ 0 := hx0
  have : ι (y.val * x.val⁻¹) • x = y := by
    rw [triv_smul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_assoc,
      inv_mul_cancel₀ hx0', mul_one]; rfl
  exact this ▸ S.smul_mem _ hx

/-- `k` is indecomposable. -/
theorem triv_indecomposable : IsIndecomposable A Triv :=
  ⟨⟨Triv.mk 0, Triv.mk 1, fun h => zero_ne_one (α := ZMod 3) h⟩, fun S _T hST =>
    (triv_simple S).imp_right fun (h : S = ⊤) => top_disjoint.mp (h ▸ hST.disjoint)⟩

/-- `k` is not projective. -/
theorem triv_not_projective : ¬ Module.Projective A Triv := fun _ => by
  obtain ⟨q, hq⟩ := mem_t_of_t_sq_smul (Triv.mk 1) (by rw [sq, mul_smul, t_smul_triv])
  exact cyc_triv.2 q hq

/-- `N1 = ann(1) = ker ε`, the augmentation ideal (`= (t)`), a model of `Ωk`. -/
noncomputable def N1 : Submodule A A := LinearMap.ker (LinearMap.toSpanSingleton A Triv (Triv.mk 1))

theorem mem_N1 (a : A) : a ∈ N1 ↔ ε a = 0 := by
  rw [N1, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, triv_smul]
  exact Iff.intro (fun h => (mul_one (ε a)).symm.trans h) (fun h => (mul_one (ε a)).trans h)

noncomputable def t1 : N1 := ⟨t, (mem_N1 t).mpr eps_t⟩

theorem cyc_N1 : CyclicGen t1 := by
  refine ⟨fun ⟨a, ha⟩ => ?_, fun ⟨m, hm⟩ h => ?_⟩
  · obtain ⟨d, rfl⟩ := ker_eps ((mem_N1 a).mp ha)
    exact ⟨d, Subtype.ext (by simp [t1, mul_comm])⟩
  · obtain ⟨d, rfl⟩ := ker_eps ((mem_N1 m).mp hm)
    have h' : t = t * (t * d) := congrArg Subtype.val h
    apply t_sq_ne_zero
    linear_combination t * h' + d * t_cube

/-- `N2 = ann_A(t) = (t²)`, a model of `Ω²k`. -/
noncomputable def N2 : Submodule A A := LinearMap.ker (LinearMap.toSpanSingleton A N1 t1)

theorem mem_N2 (a : A) : a ∈ N2 ↔ a * t = 0 := by
  rw [N2, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Subtype.val_inj]; rfl

/-- `Ω²k ≅ k`: the map `x ↦ x t²` is an isomorphism `k → N2`. -/
noncomputable def trivToN2 : Triv →ₗ[A] N2 where
  toFun x := ⟨ι x.val * t ^ 2, (mem_N2 _).mpr (by linear_combination (ι x.val) * t_cube)⟩
  map_add' x y := Subtype.ext (by
    show ι (x.val + y.val) * t ^ 2 = ι x.val * t ^ 2 + ι y.val * t ^ 2
    rw [map_add, add_mul])
  map_smul' a x := Subtype.ext (by
    show ι (ε a * x.val) * t ^ 2 = a * (ι x.val * t ^ 2)
    rw [map_mul, mul_comm (ι (ε a)), mul_assoc, ← t_sq_mul]; ring)

theorem trivToN2_bijective : Function.Bijective trivToN2 := by
  refine ⟨fun x y h => ?_, fun ⟨a, ha⟩ => ?_⟩
  · have h' : ι (x.val - y.val) * t ^ 2 = 0 := by
      have := congrArg Subtype.val h
      rw [map_sub, sub_mul]; exact sub_eq_zero.mpr this
    exact sub_eq_zero.mp (eq_zero_of_smul_t_sq h')
  · have hat : a * t = 0 := (mem_N2 a).mp ha
    obtain ⟨d, rfl⟩ := ker_eps (a := a) (eps_of_t_sq_mul (c := a) (by linear_combination t * hat))
    obtain ⟨d', rfl⟩ := ker_eps (a := d) (eps_of_t_sq_mul (c := d) (by linear_combination hat))
    refine ⟨Triv.mk (ε d'), Subtype.ext ?_⟩
    show ι (ε d') * t ^ 2 = t * (t * d')
    rw [← t_sq_mul]; ring

noncomputable def trivEquivN2 : Triv ≃ₗ[A] N2 := LinearEquiv.ofBijective _ trivToN2_bijective

/-- `Ωk ≇ k`: `t` does not kill `N1`, but kills `k`. -/
theorem N1_not_equiv_triv (e : N1 ≃ₗ[A] Triv) : False := by
  have h : t • t1 = 0 := e.injective (by rw [e.map_smul, t_smul_triv, map_zero])
  exact t_sq_ne_zero (by rw [sq]; exact congrArg Subtype.val h)

/-! ## The period of the trivial module is 2 -/

/-- The trivial module as an object of `ModuleCat A`. -/
noncomputable abbrev K : ModuleCat.{0} A := ModuleCat.of A Triv

theorem syz_K (N : ModuleCat.{0} A) (h : IsSyzygy A K N) : Nonempty (N1 ≃ₗ[A] N) := by
  obtain ⟨P, π, hπ, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := ker_cover_equiv cyc_triv hπ
  exact ⟨f.symm ≪≫ₗ e⟩

theorem syz_of_N1 (N N' : ModuleCat.{0} A) (f : N1 ≃ₗ[A] N) (h : IsSyzygy A N N') :
    Nonempty (N2 ≃ₗ[A] N') := by
  obtain ⟨P, π, hπ, ⟨e⟩⟩ := h
  obtain ⟨f'⟩ := ker_cover_equiv (cyc_N1.map f) hπ
  exact ⟨(LinearEquiv.ofEq _ _ (ker_toSpan_map f t1)).symm ≪≫ₗ f'.symm ≪≫ₗ e⟩

/-- No first syzygy of `k` is isomorphic to `k`. -/
theorem not_iterSyz_one : ¬ IterSyz A 1 K K := by
  rintro ⟨N, h, ⟨e⟩⟩
  obtain ⟨f⟩ := syz_K N h
  exact N1_not_equiv_triv (f ≪≫ₗ e)

/-- Every second syzygy of `k` (for every choice of projective covers) is isomorphic to `k`. -/
theorem iterSyz_two_any (N : ModuleCat.{0} A) (h : IterSyz A 2 K N) : Nonempty (N ≃ₗ[A] Triv) := by
  obtain ⟨N', h1, N'', h2, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := syz_K N' h1
  obtain ⟨f'⟩ := syz_of_N1 N' N'' f h2
  exact ⟨e.symm ≪≫ₗ f'.symm ≪≫ₗ trivEquivN2.symm⟩

theorem iterSyz_two : IterSyz A 2 K K :=
  ⟨ModuleCat.of A N1, ⟨ModuleCat.of A A, LinearMap.toSpanSingleton A Triv (Triv.mk 1),
      toSpan_isCover cyc_triv, ⟨LinearEquiv.refl _ _⟩⟩,
    ModuleCat.of A N2, ⟨ModuleCat.of A A, LinearMap.toSpanSingleton A N1 t1,
      toSpan_isCover cyc_N1, ⟨LinearEquiv.refl _ _⟩⟩, ⟨trivEquivN2.symm⟩⟩

/-- The trivial `F₃[C₃]`-module has minimal syzygy period `2`. -/
theorem period_K : HasPeriod A K 2 :=
  ⟨two_pos, iterSyz_two, fun m h0 h2 => by
    obtain rfl : m = 1 := by omega
    exact not_iterSyz_one⟩

/-! ## Subgroups of `C₃` and the conjecture -/

theorem not_two_dvd_card (D : Subgroup G) : ¬ 2 ∣ Nat.card D := fun h => by
  have h3 : Nat.card G = 3 := by simp [Nat.card_eq_fintype_card]
  have := Nat.dvd_trans h (h3 ▸ D.card_subgroup_dvd_card)
  omega

/-- The first clause for `F_p[H]`, for finitely generated indecomposable non-projective periodic
modules, weakened: "the defect group `D` of the block of `M`" is replaced by "some subgroup
`D ≤ H`" (a defect group is a subgroup of `H`). Reading: every prime factor `q`
of the minimal period divides some prime factor `r` of `|D|`. -/
def Clause1 (p : ℕ) [Fact p.Prime] (H : Type) [Group H] : Prop :=
  ∀ (M : ModuleCat.{0} (MonoidAlgebra (ZMod p) H)) (n : ℕ),
    Module.Finite (MonoidAlgebra (ZMod p) H) M → IsIndecomposable (MonoidAlgebra (ZMod p) H) M →
    ¬ Module.Projective (MonoidAlgebra (ZMod p) H) M → HasPeriod _ M n →
    ∃ D : Subgroup H, ∀ q ∈ n.primeFactors, ∃ r ∈ (Nat.card D).primeFactors, q ∣ r

/-- Variant reading: every prime factor of the minimal period divides `|D|`. -/
def Clause1' (p : ℕ) [Fact p.Prime] (H : Type) [Group H] : Prop :=
  ∀ (M : ModuleCat.{0} (MonoidAlgebra (ZMod p) H)) (n : ℕ),
    Module.Finite (MonoidAlgebra (ZMod p) H) M → IsIndecomposable (MonoidAlgebra (ZMod p) H) M →
    ¬ Module.Projective (MonoidAlgebra (ZMod p) H) M → HasPeriod _ M n →
    ∃ D : Subgroup H, ∀ q ∈ n.primeFactors, q ∣ Nat.card D

/-- The trivial `F₃[C₃]`-module is finitely generated, indecomposable and not projective, has
minimal period `2`, every second syzygy of it is isomorphic to it, and `2` divides no prime factor
of the order of any subgroup of `C₃`. -/
theorem trivial_module_counterexample :
    Module.Finite A Triv ∧ IsIndecomposable A Triv ∧ ¬ Module.Projective A Triv ∧
    HasPeriod A K 2 ∧ (∀ N, IterSyz A 2 K N → Nonempty (N ≃ₗ[A] Triv)) ∧
      ∀ D : Subgroup G, ∀ r ∈ (Nat.card D).primeFactors, ¬ 2 ∣ r :=
  ⟨inferInstance, triv_indecomposable, triv_not_projective, period_K, iterSyz_two_any,
    fun D _ hr h2 =>
    not_two_dvd_card D (h2.trans (Nat.dvd_of_mem_primeFactors hr))⟩

/-- Main theorem: the first clause fails for `p = 3`, `G = C₃`. -/
theorem conjecture_4053_false : ¬ Clause1 3 G := fun h => by
  obtain ⟨D, hD⟩ := h K 2 inferInstance triv_indecomposable triv_not_projective period_K
  obtain ⟨r, hr, h2⟩ := hD 2 (by simp [Nat.prime_two.primeFactors])
  exact trivial_module_counterexample.2.2.2.2.2 D r hr h2

theorem conjecture_4053_false' : ¬ Clause1' 3 G := fun h => by
  obtain ⟨D, hD⟩ := h K 2 inferInstance triv_indecomposable triv_not_projective period_K
  exact not_two_dvd_card D (hD 2 (by simp [Nat.prime_two.primeFactors]))

/-- Hence the conjecture (first clause and any second clause) fails. -/
theorem conjecture_4053_conj_false (Clause2 : Prop) : ¬ (Clause1 3 G ∧ Clause2) :=
  fun h => conjecture_4053_false h.1

end C4053
