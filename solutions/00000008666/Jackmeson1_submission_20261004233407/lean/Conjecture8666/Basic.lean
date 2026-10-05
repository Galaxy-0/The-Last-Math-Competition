import Mathlib

/-!
# Conjecture 00000008666: the "finite list law" for non-Hamiltonian Cayley digraphs is false

The conjecture is a conjunction of four laws. Its second clause (the finite list law) says that the
exceptions, i.e. the Cayley digraphs of finite groups without a Hamiltonian cycle, form a finite list.

We formalize Cayley digraphs and directed Hamiltonian cycles, and prove Rankin's coset argument:
for every odd `n ≥ 3` the Cayley digraph of `ℤ/2 × ℤ/n` (a cyclic group of order `2n`) with the
generating set `{(1,0), (0,1)}` has no directed Hamiltonian cycle. These exceptions have unbounded
order, so they do not form a finite list, and the conjunction is false whatever the other three
clauses mean.
-/

open Function

namespace Conjecture8666

/-! ## Definitions -/

/-- The Cayley digraph `Cay(G, S)` of a group `G` with connection set `S ⊆ G`: the vertices are the
elements of `G`, and there is an arc `g → g * s` for every `g ∈ G` and `s ∈ S`. -/
def cayleyDigraph (G : Type*) [Mul G] (S : Set G) : Digraph G where
  Adj g h := ∃ s ∈ S, g * s = h

/-- Sanity check: the underlying undirected simple graph of `Cay(G, S)` (forget orientations and
loops) is Mathlib's Cayley graph `SimpleGraph.mulCayley S`. -/
theorem mulCayley_adj_iff {G : Type*} [Mul G] (S : Set G) (u v : G) :
    (SimpleGraph.mulCayley S).Adj u v ↔
      u ≠ v ∧ ((cayleyDigraph G S).Adj u v ∨ (cayleyDigraph G S).Adj v u) := by
  rw [SimpleGraph.mulCayley_adj']
  simp only [cayleyDigraph]
  constructor
  · rintro ⟨h, s, hs, h1 | h1⟩
    · exact ⟨h, Or.inl ⟨s, hs, h1⟩⟩
    · exact ⟨h, Or.inr ⟨s, hs, h1.symm⟩⟩
  · rintro ⟨h, ⟨s, hs, h1⟩ | ⟨s, hs, h1⟩⟩
    · exact ⟨h, s, hs, Or.inl h1⟩
    · exact ⟨h, s, hs, Or.inr h1.symm⟩

/-- A directed Hamiltonian cycle of a finite digraph `D` with `m = |V|` vertices: an enumeration
`v 0, v 1, …, v (m-1)` that lists every vertex exactly once (`v : Fin m → V` is a bijection), with
an arc `v i → v (i+1)` for each `i < m - 1` and the closing arc `v (m-1) → v 0`. Here `finRotate m`
is the map `i ↦ i + 1 (mod m)` on `Fin m` (see `finRotate_val`). -/
def IsHamiltonianCycle {V : Type*} [Fintype V] (D : Digraph V)
    (v : Fin (Fintype.card V) → V) : Prop :=
  Bijective v ∧ ∀ i, D.Adj (v i) (v (finRotate _ i))

/-- A finite digraph is Hamiltonian if it has a directed Hamiltonian cycle. -/
def IsHamiltonian {V : Type*} [Fintype V] (D : Digraph V) : Prop :=
  ∃ v, IsHamiltonianCycle D v

/-- `finRotate m` is the successor map `i ↦ i + 1 (mod m)` on `Fin m`. -/
theorem finRotate_val {m : ℕ} (i : Fin m) : (finRotate m i).val = (i.val + 1) % m := by
  cases m with
  | zero => exact i.elim0
  | succ k =>
    rw [coe_finRotate]
    split_ifs with h
    · subst h; simp
    · have : i.val < k := by
        have := i.isLt
        have hne : i.val ≠ k := fun h' => h (Fin.ext h')
        omega
      rw [Nat.mod_eq_of_lt (by omega)]

/-! ## Rankin's coset argument -/

section Rankin

variable {G : Type*} [CommGroup G]

/-- Rankin's key step. Let `σ` be an injective successor map whose steps are all `a` or `b`
(`a ≠ b`). If the step at `x` is `a`, then the step at `x * (a * b⁻¹)` is also `a`: otherwise
`σ (x a b⁻¹) = x a b⁻¹ b = x a = σ x`, contradicting injectivity. -/
theorem step_propagates (σ : G → G) (hσ : Injective σ) {a b : G} (hab : a ≠ b)
    (hstep : ∀ x, σ x = x * a ∨ σ x = x * b) {x : G} (hx : σ x = x * a) :
    σ (x * (a * b⁻¹)) = x * (a * b⁻¹) * a := by
  rcases hstep (x * (a * b⁻¹)) with h | h
  · exact h
  · exfalso
    have h1 : σ (x * (a * b⁻¹)) = σ x := by
      rw [h, hx]; group
    have h2 : x * (a * b⁻¹) = x := hσ h1
    have h3 : a * b⁻¹ = 1 := by simpa using h2
    exact hab (mul_inv_eq_one.mp h3)

/-- If `a * b⁻¹` generates `G` and one step of `σ` is `a`, then every step of `σ` is `a`. -/
theorem step_const [Finite G] (σ : G → G) (hσ : Injective σ) {a b : G} (hab : a ≠ b)
    (hstep : ∀ x, σ x = x * a ∨ σ x = x * b)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers (a * b⁻¹))
    {x : G} (hx : σ x = x * a) (y : G) : σ y = y * a := by
  have key : ∀ k : ℕ, σ (x * (a * b⁻¹) ^ k) = x * (a * b⁻¹) ^ k * a := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      exact step_propagates σ hσ hab hstep ih
  obtain ⟨k, hk⟩ :=
    (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hgen (x⁻¹ * y)))
  have hy : y = x * (a * b⁻¹) ^ k := by rw [hk]; group
  rw [hy]; exact key k

/-- If every step of an injective enumeration `v` of `G` (cyclically indexed) is right
multiplication by the same `c`, then `v k = v 0 * c ^ k`, hence `|G| ≤ orderOf c`. -/
theorem card_le_orderOf_of_const [Fintype G] {v : Fin (Fintype.card G) → G} (hv : Injective v)
    {c : G} (hc : ∀ i, v (finRotate _ i) = v i * c) : Fintype.card G ≤ orderOf c := by
  have hm : 0 < Fintype.card G := Fintype.card_pos
  have hk : ∀ k (hk : k < Fintype.card G), v ⟨k, hk⟩ = v ⟨0, hm⟩ * c ^ k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk1
      have h1 := hc ⟨k, by omega⟩
      have hrot : finRotate (Fintype.card G) ⟨k, by omega⟩ = ⟨k + 1, hk1⟩ :=
        Fin.ext (by rw [finRotate_val]; exact Nat.mod_eq_of_lt hk1)
      rw [hrot] at h1
      rw [h1, ih (by omega), pow_succ, mul_assoc]
  by_contra hlt
  replace hlt := not_le.1 hlt
  have h0 := hk (orderOf c) hlt
  rw [pow_orderOf_eq_one, mul_one] at h0
  have h1 := Fin.mk.inj_iff.1 (hv h0)
  exact (orderOf_pos c).ne' h1

/-- **Rankin's theorem (two generators).** Let `G` be a finite abelian group and `a ≠ b` in `G`
such that `a * b⁻¹` generates `G`, and `a`, `b` both have order `< |G|`. Then the Cayley digraph
`Cay(G, {a, b})` has no directed Hamiltonian cycle. -/
theorem rankin [Fintype G] {a b : G} (hab : a ≠ b)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers (a * b⁻¹))
    (ha : orderOf a < Fintype.card G) (hb : orderOf b < Fintype.card G) :
    ¬ IsHamiltonian (cayleyDigraph G {a, b}) := by
  rintro ⟨v, hv, hadj⟩
  let e := Equiv.ofBijective v hv
  let σ : G → G := fun x => v (finRotate _ (e.symm x))
  have hσinj : Injective σ :=
    hv.1.comp ((finRotate _).injective.comp e.symm.injective)
  have hσv : ∀ i, σ (v i) = v (finRotate _ i) := by
    intro i
    have : e.symm (v i) = i := e.symm_apply_apply i
    simp only [σ, this]
  have hstep : ∀ x, σ x = x * a ∨ σ x = x * b := by
    intro x
    obtain ⟨i, rfl⟩ := hv.2 x
    obtain ⟨s, hs, h⟩ := hadj i
    rw [hσv, ← h]
    rcases hs with hs | hs
    · left; rw [hs]
    · right; rw [Set.mem_singleton_iff.1 hs]
  have hgen' : ∀ g : G, g ∈ Subgroup.zpowers (b * a⁻¹) := by
    intro g
    have : b * a⁻¹ = (a * b⁻¹)⁻¹ := by group
    rw [this, Subgroup.zpowers_inv]
    exact hgen g
  have hm : 0 < Fintype.card G := Fintype.card_pos
  rcases hstep (v ⟨0, hm⟩) with h | h
  · have hall := step_const σ hσinj hab hstep hgen h
    have := card_le_orderOf_of_const hv.1 (c := a) (fun i => by rw [← hσv, hall])
    omega
  · have hall := step_const σ hσinj hab.symm (fun x => (hstep x).symm) hgen' h
    have := card_le_orderOf_of_const hv.1 (c := b) (fun i => by rw [← hσv, hall])
    omega

end Rankin

/-! ## The infinite family `Cay(ℤ/2 × ℤ/n, {(1,0), (0,1)})`, `n` odd -/

section Family

variable (n : ℕ) [NeZero n]

/-- The group `ℤ/2 × ℤ/n`, written multiplicatively (cyclic of order `2n` when `n` is odd). -/
abbrev Gn := Multiplicative (ZMod 2 × ZMod n)

/-- The generator `a = (1, 0)`. -/
def genA : Gn n := Multiplicative.ofAdd (1, 0)

/-- The generator `b = (0, 1)`. -/
def genB : Gn n := Multiplicative.ofAdd (0, 1)

theorem card_Gn : Fintype.card (Gn n) = 2 * n := by
  simp [Gn, ZMod.card]

omit [NeZero n] in
theorem orderOf_genA : orderOf (genA n) = 2 := by
  rw [genA, orderOf_ofAdd_eq_addOrderOf, Prod.addOrderOf_mk, ZMod.addOrderOf_one, addOrderOf_zero,
    Nat.lcm_one_right]

omit [NeZero n] in
theorem orderOf_genB : orderOf (genB n) = n := by
  rw [genB, orderOf_ofAdd_eq_addOrderOf, Prod.addOrderOf_mk, ZMod.addOrderOf_one, addOrderOf_zero,
    Nat.lcm_one_left]

omit [NeZero n] in
theorem orderOf_genA_div_genB (hn : Odd n) : orderOf (genA n * (genB n)⁻¹) = 2 * n := by
  have : genA n * (genB n)⁻¹ = Multiplicative.ofAdd ((1 : ZMod 2), (-1 : ZMod n)) := by
    simp only [genA, genB, ← ofAdd_neg, ← ofAdd_add, Prod.neg_mk, Prod.mk_add_mk, neg_zero,
      add_zero, zero_add]
  rw [this, orderOf_ofAdd_eq_addOrderOf, Prod.addOrderOf_mk, addOrderOf_neg, ZMod.addOrderOf_one,
    ZMod.addOrderOf_one]
  exact Nat.Coprime.lcm_eq_mul (Nat.coprime_two_left.2 hn)

theorem zpowers_eq_top (hn : Odd n) : Subgroup.zpowers (genA n * (genB n)⁻¹) = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, orderOf_genA_div_genB n hn, Nat.card_eq_fintype_card, card_Gn]

/-- `{a, b}` generates `ℤ/2 × ℤ/n` (`n` odd). -/
theorem closure_gens (hn : Odd n) : Subgroup.closure ({genA n, genB n} : Set (Gn n)) = ⊤ := by
  rw [eq_top_iff, ← zpowers_eq_top n hn, Subgroup.zpowers_le]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))

omit [NeZero n] in
/-- The identity is not a generator (both generators have order `> 1`). -/
theorem one_notMem_gens (h3 : 3 ≤ n) : (1 : Gn n) ∉ ({genA n, genB n} : Set (Gn n)) := by
  intro h
  rcases h with h | h
  · have := orderOf_genA n
    rw [← h, orderOf_one] at this
    omega
  · have := orderOf_genB n
    rw [← Set.mem_singleton_iff.1 h, orderOf_one] at this
    omega

/-- **Rankin's family.** For odd `n ≥ 3`, the Cayley digraph of `ℤ/2 × ℤ/n` with generators
`(1,0)` and `(0,1)` has no directed Hamiltonian cycle. -/
theorem rankin_family (hn : Odd n) (h3 : 3 ≤ n) :
    ¬ IsHamiltonian (cayleyDigraph (Gn n) {genA n, genB n}) := by
  have hab : genA n ≠ genB n := by
    intro h
    have h1 := orderOf_genA n
    rw [h, orderOf_genB] at h1
    subst h1
    exact (Nat.not_odd_iff_even.2 even_two) hn
  apply rankin hab (fun g => (zpowers_eq_top n hn) ▸ Subgroup.mem_top g)
  · rw [orderOf_genA, card_Gn]; omega
  · rw [orderOf_genB, card_Gn]; omega

end Family

/-! ## The conjecture's clauses and their refutation -/

/-- The orders `|G|` of the exceptions: finite groups `G` with a generating set `S` (not containing
the identity) whose Cayley digraph `Cay(G, S)` has no directed Hamiltonian cycle. -/
def exceptionOrders : Set ℕ :=
  {m | ∃ (G : Type) (_ : Group G) (_ : Fintype G) (S : Set G),
      Subgroup.closure S = ⊤ ∧ (1 : G) ∉ S ∧ ¬ IsHamiltonian (cayleyDigraph G S) ∧
        Fintype.card G = m}

/-- Every `2n` with `n ≥ 3` odd is the order of an exception. -/
theorem two_mul_mem_exceptionOrders {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) :
    2 * n ∈ exceptionOrders := by
  have : NeZero n := ⟨by omega⟩
  exact ⟨Gn n, inferInstance, inferInstance, {genA n, genB n}, closure_gens n hn,
    one_notMem_gens n h3, rankin_family n hn h3, card_Gn n⟩

/-- There are exceptions of arbitrarily large order: the exceptions are infinitely many
(pairwise non-isomorphic, since their orders differ). -/
theorem exceptionOrders_infinite : exceptionOrders.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hmem := two_mul_mem_exceptionOrders (n := 2 * B + 3) ⟨B + 1, by ring⟩ (by omega)
  have := hB hmem
  omega

/-- Clause 2 of the conjecture (finite list law): the exceptions (Cayley digraphs of finite groups
without a Hamiltonian cycle) form a finite list. A finite list of finite groups has finitely many
orders, so the clause implies `exceptionOrders.Finite`; we take this weakest consequence as the
formal clause. -/
def FiniteListLaw : Prop :=
  exceptionOrders.Finite

/-- The finite list law is false. -/
theorem finiteListLaw_false : ¬ FiniteListLaw :=
  exceptionOrders_infinite

/-- Clause 1 read for Cayley digraphs: every Cayley digraph of a finite group with respect to a
generating set has a directed Hamiltonian cycle. (Under the undirected reading this is the open
Lovász-type conjecture, which is not addressed.) -/
def DirectedHamiltonianLaw : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (S : Set G), Subgroup.closure S = ⊤ →
    IsHamiltonian (cayleyDigraph G S)

/-- The directed reading of clause 1 is false as well (already for `ℤ/2 × ℤ/3 ≅ ℤ/6`). -/
theorem directedHamiltonianLaw_false : ¬ DirectedHamiltonianLaw := fun h =>
  rankin_family 3 (by decide) le_rfl (h (Gn 3) _ (closure_gens 3 (by decide)))

/-- **Main theorem.** The conjecture is the conjunction of the Hamiltonian law (`H`, in any
reading), the finite list law, the PSL unresolved law (`P`) and the lexico law (`L`). Since the
finite list law is false, the conjunction is false whatever `H`, `P` and `L` mean. -/
theorem conjecture8666_false (H P L : Prop) : ¬ (H ∧ FiniteListLaw ∧ P ∧ L) :=
  fun h => finiteListLaw_false h.2.1

end Conjecture8666
