import Mathlib

/-!
# Conjecture 00000001195: Kronecker power-sum "orthogonality" fails

Conjecture (literal): for the inner (Kronecker) product `*` of symmetric functions,
`⟨p_λ, p_μ * p_ν⟩ = z_λ · δ`, where `δ` is a Kronecker delta.

We work in degree `2`. By the standard restriction isomorphism, the degree-`2` part of the ring of
symmetric functions is the degree-`2` part of the ring of symmetric polynomials in `2` variables,
`MvPolynomial (Fin 2) ℚ`, with `p_λ`, `h_λ`, `m_λ` going to Mathlib's `psumPart`, `hsymmPart`,
`msymm`.

* The Hall inner product is pinned down by its defining duality `⟨h_λ, m_μ⟩ = δ_{λμ}`
  (`IsHallInner`).
* The Kronecker product is pinned down by the Frobenius characteristic map
  `ch φ = (1/2!) ∑_{w ∈ S₂} φ(w) p_{ρ(w)}` (`frob`, with `ρ(w) = Equiv.Perm.partition w` the cycle
  type including fixed points): `ch φ * ch ψ = ch (φ ψ)` for class functions `φ, ψ` on `S₂`
  (`IsKronecker`).

For every such pair (and such pairs exist) we prove `⟨p_(2), p_(2) * p_(2)⟩ = 4 = z_(2)^2`, while
`z_(2) = 2`, so `z_(2) · δ ∈ {0, 2}` for every `δ ∈ {0, 1}`.
-/

open MvPolynomial

noncomputable section

namespace C1195

/-- The ambient ring: polynomials in two variables over `ℚ`. -/
abbrev P := MvPolynomial (Fin 2) ℚ

/-- The partition `(2)` of `2`. -/
def two : Nat.Partition 2 where
  parts := {2}
  parts_pos := by intro i hi; simp at hi; omega
  parts_sum := by simp

/-- The partition `(1,1)` of `2`. -/
def oneOne : Nat.Partition 2 where
  parts := {1, 1}
  parts_pos := by intro i hi; simp at hi; omega
  parts_sum := by simp

lemma two_ne_oneOne : two ≠ oneOne := by
  intro h
  have := congrArg Nat.Partition.parts h
  simp [two, oneOne] at this

/-- `(2)` and `(1,1)` are the only partitions of `2`. -/
lemma partition_two_cases (l : Nat.Partition 2) : l = two ∨ l = oneOne := by
  rcases l with ⟨⟨L⟩, hpos, hsum⟩
  have hpos' : ∀ i ∈ L, 0 < i := fun i hi => hpos (by simpa using hi)
  simp only [Multiset.quot_mk_to_coe'', Multiset.sum_coe] at hsum
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, L⟩⟩⟩
  · simp at hsum
  · left
    simp at hsum
    subst hsum
    rfl
  · right
    have ha := hpos' a (by simp)
    have hb := hpos' b (by simp)
    simp at hsum
    obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 1 := by omega
    rfl
  · exfalso
    have ha := hpos' a (by simp)
    have hb := hpos' b (by simp)
    have hc := hpos' c (by simp)
    simp at hsum
    omega

/-- `z_λ = ∏_i i^{m_i} m_i!`, where `m_i` is the multiplicity of `i` in `λ`. -/
def zee {n : ℕ} (l : n.Partition) : ℕ :=
  ∏ i ∈ l.parts.toFinset, i ^ l.parts.count i * (l.parts.count i).factorial

lemma zee_two : zee two = 2 := by
  simp [zee, two]

/-! ## The classical bases in two variables -/

lemma psumPart_two : psumPart (Fin 2) ℚ two = X 0 ^ 2 + X 1 ^ 2 := by
  simp [psumPart, two, psum, Fin.sum_univ_two]

lemma hsymmPart_two : hsymmPart (Fin 2) ℚ two = X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 := by
  have : (Finset.univ : Finset (Sym (Fin 2) 2)) =
      {Sym.replicate 2 0, (0 : Fin 2) ::ₛ (1 : Fin 2) ::ₛ Sym.nil, Sym.replicate 2 1} := by decide
  simp only [hsymmPart, two, Multiset.map_singleton, Multiset.prod_singleton, hsymm, this]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [Sym.replicate, Sym.coe_cons, Sym.coe_nil]
  ring

lemma hsymmPart_oneOne : hsymmPart (Fin 2) ℚ oneOne = (X 0 + X 1) ^ 2 := by
  simp [hsymmPart, oneOne, Fin.sum_univ_two]
  ring

lemma msymm_two : msymm (Fin 2) ℚ two = X 0 ^ 2 + X 1 ^ 2 := by
  rw [msymm, ← Finset.sum_subtype (Finset.univ.filter (fun a : Sym (Fin 2) 2 =>
      Nat.Partition.ofSym a = two)) (by simp) (fun a : Sym (Fin 2) 2 => (a.1.map X).prod)]
  have : (Finset.univ.filter (fun a : Sym (Fin 2) 2 => Nat.Partition.ofSym a = two)) =
      {Sym.replicate 2 0, Sym.replicate 2 1} := by decide
  rw [this, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [Sym.replicate]
  ring

lemma msymm_oneOne : msymm (Fin 2) ℚ oneOne = X 0 * X 1 := by
  rw [msymm, ← Finset.sum_subtype (Finset.univ.filter (fun a : Sym (Fin 2) 2 =>
      Nat.Partition.ofSym a = oneOne)) (by simp) (fun a : Sym (Fin 2) 2 => (a.1.map X).prod)]
  have : (Finset.univ.filter (fun a : Sym (Fin 2) 2 => Nat.Partition.ofSym a = oneOne)) =
      {(0 : Fin 2) ::ₛ (1 : Fin 2) ::ₛ Sym.nil} := by decide
  rw [this, Finset.sum_singleton]
  simp [Sym.coe_cons, Sym.coe_nil]

/-! ## The Hall inner product (degree 2) -/

/-- `B` is the Hall inner product on the degree-2 part: `⟨h_λ, m_μ⟩ = δ_{λμ}` for `λ, μ ⊢ 2`. -/
def IsHallInner (B : P →ₗ[ℚ] P →ₗ[ℚ] ℚ) : Prop :=
  ∀ l μ : Nat.Partition 2,
    B (hsymmPart (Fin 2) ℚ l) (msymm (Fin 2) ℚ μ) = if l = μ then 1 else 0

lemma psumPart_two_eq_h : psumPart (Fin 2) ℚ two =
    (2 : ℚ) • hsymmPart (Fin 2) ℚ two - hsymmPart (Fin 2) ℚ oneOne := by
  rw [psumPart_two, hsymmPart_two, hsymmPart_oneOne, two_smul]
  ring

/-- Under any Hall inner product, `⟨p_(2), p_(2)⟩ = 2`. -/
lemma hall_p2_p2 {B : P →ₗ[ℚ] P →ₗ[ℚ] ℚ} (hB : IsHallInner B) :
    B (psumPart (Fin 2) ℚ two) (psumPart (Fin 2) ℚ two) = 2 := by
  have hm : psumPart (Fin 2) ℚ two = msymm (Fin 2) ℚ two := by rw [psumPart_two, msymm_two]
  have e : B (psumPart (Fin 2) ℚ two) (psumPart (Fin 2) ℚ two) =
      B ((2 : ℚ) • hsymmPart (Fin 2) ℚ two - hsymmPart (Fin 2) ℚ oneOne) (msymm (Fin 2) ℚ two) := by
    rw [← psumPart_two_eq_h, hm]
  rw [e, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hB, hB,
    if_pos rfl, if_neg (Ne.symm two_ne_oneOne)]
  norm_num

/-! ## The Frobenius characteristic map and the Kronecker product (degree 2) -/

/-- The Frobenius characteristic map `ch φ = (1/2!) ∑_{w ∈ S₂} φ(w) p_{ρ(w)}`, where `ρ(w)` is the
cycle type of `w` (fixed points counted as parts `1`). -/
def frob (φ : Equiv.Perm (Fin 2) → ℚ) : P :=
  ((Nat.factorial 2 : ℕ) : ℚ)⁻¹ • ∑ w : Equiv.Perm (Fin 2), φ w • psumPart (Fin 2) ℚ w.partition

/-- Class functions on `S₂`. -/
def IsClassFun (φ : Equiv.Perm (Fin 2) → ℚ) : Prop :=
  ∀ g k : Equiv.Perm (Fin 2), φ (k * g * k⁻¹) = φ g

/-- `K` is the Kronecker (inner) product on the degree-2 part: `ch φ * ch ψ = ch (φ ψ)`. -/
def IsKronecker (K : P →ₗ[ℚ] P →ₗ[ℚ] P) : Prop :=
  ∀ φ ψ : Equiv.Perm (Fin 2) → ℚ, IsClassFun φ → IsClassFun ψ → K (frob φ) (frob ψ) = frob (φ * ψ)

lemma univ_perm_two : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
  decide

lemma parts_partition_one : (1 : Equiv.Perm (Fin 2)).partition.parts = {1, 1} := by
  simp [Equiv.Perm.parts_partition]

lemma parts_partition_swap : (Equiv.swap (0 : Fin 2) 1).partition.parts = {2} := by
  rw [Equiv.Perm.parts_partition, (Equiv.Perm.isCycle_swap (by decide)).cycleType,
    Equiv.Perm.card_support_swap (by decide)]
  simp

lemma frob_eq (φ : Equiv.Perm (Fin 2) → ℚ) :
    frob φ = (2 : ℚ)⁻¹ • (φ 1 • (X 0 + X 1) ^ 2 + φ (Equiv.swap 0 1) • (X 0 ^ 2 + X 1 ^ 2)) := by
  rw [frob, univ_perm_two, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [psumPart, parts_partition_one, parts_partition_swap]
  simp [psum, Fin.sum_univ_two, sq]

lemma frob_smul (c : ℚ) (φ : Equiv.Perm (Fin 2) → ℚ) : frob (c • φ) = c • frob φ := by
  rw [frob_eq, frob_eq]
  simp only [Pi.smul_apply, smul_eq_mul, smul_add, mul_smul]
  module

open Classical in
/-- `z_λ` times the indicator of the conjugacy class of cycle type `λ`. -/
def classInd (l : Nat.Partition 2) (w : Equiv.Perm (Fin 2)) : ℚ :=
  if w.partition.parts = l.parts then (zee l : ℚ) else 0

lemma classInd_isClassFun (l : Nat.Partition 2) : IsClassFun (classInd l) := by
  intro g k
  have : (k * g * k⁻¹).partition = g.partition :=
    (Equiv.Perm.partition_eq_of_isConj.mp (isConj_iff.mpr ⟨k, rfl⟩)).symm
  unfold classInd
  rw [this]

/-- `p_(2) = ch (z_(2) · 1_{(2)})`. -/
lemma frob_classInd_two : frob (classInd two) = psumPart (Fin 2) ℚ two := by
  rw [frob_eq, psumPart_two]
  have h1 : classInd two 1 = 0 := by
    rw [classInd, if_neg]; rw [parts_partition_one]; simp only [two]; decide
  have h2 : classInd two (Equiv.swap 0 1) = 2 := by
    rw [classInd, if_pos (by rw [parts_partition_swap]; rfl), zee_two]; norm_num
  rw [h1, h2]
  module

/-- Under any Kronecker product, `p_(2) * p_(2) = 2 • p_(2)`. -/
lemma kron_p2_p2 {K : P →ₗ[ℚ] P →ₗ[ℚ] P} (hK : IsKronecker K) :
    K (psumPart (Fin 2) ℚ two) (psumPart (Fin 2) ℚ two) = (2 : ℚ) • psumPart (Fin 2) ℚ two := by
  rw [← frob_classInd_two, hK _ _ (classInd_isClassFun two) (classInd_isClassFun two)]
  have : classInd two * classInd two = (2 : ℚ) • classInd two := by
    funext w
    simp only [classInd, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, zee_two]
    split_ifs <;> norm_num
  rw [this, frob_smul]

/-! ## Existence: explicit Hall inner product and Kronecker product -/

/-- Evaluation at a point, as a linear functional. -/
def ev (v : Fin 2 → ℚ) : P →ₗ[ℚ] ℚ := (aeval v).toLinearMap

/-- On degree-2 symmetric polynomials, `ca f` is the coefficient of `m_(2)`. -/
def ca : P →ₗ[ℚ] ℚ := ev ![1, 0]

/-- On degree-2 symmetric polynomials, `cb f` is the coefficient of `m_(1,1)`. -/
def cb : P →ₗ[ℚ] ℚ := ev ![1, 1] - (2 : ℚ) • ev ![1, 0]

/-- An explicit bilinear form satisfying the Hall duality. -/
def B0 : P →ₗ[ℚ] P →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun f g => (2 * ca f - cb f) * ca g + (cb f - ca f) * cb g)
    (by intros; simp only [map_add]; ring) (by intros; simp only [map_smul, smul_eq_mul]; ring)
    (by intros; simp only [map_add]; ring) (by intros; simp only [map_smul, smul_eq_mul]; ring)

/-- An explicit bilinear map satisfying the Frobenius definition of the Kronecker product. -/
def K0 : P →ₗ[ℚ] P →ₗ[ℚ] P :=
  LinearMap.mk₂ ℚ (fun F G => (2 : ℚ)⁻¹ • ((cb F * cb G) • (X 0 + X 1) ^ 2 +
      ((2 * ca F - cb F) * (2 * ca G - cb G)) • (X 0 ^ 2 + X 1 ^ 2)))
    (by intros; simp only [map_add]; module) (by intros; simp only [map_smul, smul_eq_mul]; module)
    (by intros; simp only [map_add]; module) (by intros; simp only [map_smul, smul_eq_mul]; module)

lemma B0_isHall : IsHallInner B0 := by
  intro l μ
  rcases partition_two_cases l with rfl | rfl <;> rcases partition_two_cases μ with rfl | rfl <;>
    simp [B0, ca, cb, ev, hsymmPart_two, hsymmPart_oneOne, msymm_two, msymm_oneOne,
      two_ne_oneOne, Ne.symm two_ne_oneOne] <;> norm_num

lemma ca_frob (φ : Equiv.Perm (Fin 2) → ℚ) : ca (frob φ) = (φ 1 + φ (Equiv.swap 0 1)) / 2 := by
  rw [frob_eq]; simp [ca, ev]; ring

lemma cb_frob (φ : Equiv.Perm (Fin 2) → ℚ) : cb (frob φ) = φ 1 := by
  rw [frob_eq]; simp [cb, ev]; ring

lemma K0_isKronecker : IsKronecker K0 := by
  intro φ ψ _ _
  simp only [K0, LinearMap.mk₂_apply, ca_frob, cb_frob]
  rw [frob_eq]
  simp only [Pi.mul_apply]
  congr 1
  module

/-! ## Main theorem -/

/-- **Conjecture 00000001195 is false.** Hall inner products and Kronecker products (in the above
defining senses) exist, and for every such pair `⟨p_(2), p_(2) * p_(2)⟩ = 4 = z_(2)^2`, while
`z_(2) = 2`; hence `⟨p_λ, p_μ * p_ν⟩ ≠ z_λ · δ` at `λ = μ = ν = (2)` for every `δ ∈ {0, 1}`. -/
theorem conjecture_1195_false :
    (∃ B, IsHallInner B) ∧ (∃ K, IsKronecker K) ∧
    ∀ B K, IsHallInner B → IsKronecker K →
      B (psumPart (Fin 2) ℚ two) (K (psumPart (Fin 2) ℚ two) (psumPart (Fin 2) ℚ two)) =
          (zee two : ℚ) ^ 2 ∧ zee two = 2 ∧
      ∀ δ : ℚ, (δ = 0 ∨ δ = 1) →
        B (psumPart (Fin 2) ℚ two) (K (psumPart (Fin 2) ℚ two) (psumPart (Fin 2) ℚ two)) ≠
          (zee two : ℚ) * δ := by
  refine ⟨⟨B0, B0_isHall⟩, ⟨K0, K0_isKronecker⟩, fun B K hB hK => ?_⟩
  have hval : B (psumPart (Fin 2) ℚ two) (K (psumPart (Fin 2) ℚ two) (psumPart (Fin 2) ℚ two)) =
      4 := by
    rw [kron_p2_p2 hK, map_smul, hall_p2_p2 hB]; norm_num
  refine ⟨by rw [hval, zee_two]; norm_num, zee_two, fun δ hδ => ?_⟩
  rw [hval, zee_two]
  rcases hδ with rfl | rfl <;> norm_num

end C1195
