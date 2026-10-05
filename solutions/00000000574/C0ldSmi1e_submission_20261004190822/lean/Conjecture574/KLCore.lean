import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Polynomial

namespace Conjecture574

variable {L : Type*} [Fintype L] [PartialOrder L]
  [DecidableRel ((· ≤ ·) : L → L → Prop)]

/-- All elements of the actual order interval, including both endpoints. -/
def interval (a b : L) : Finset L :=
  Finset.univ.filter fun c => a ≤ c ∧ c ≤ b

@[simp] theorem mem_interval (a b c : L) : c ∈ interval a b ↔ a ≤ c ∧ c ≤ b := by
  simp [interval]

/-- Coefficient form of the strict KL degree bound `degree p < d/2`.
It includes the zero polynomial without assigning it an artificial natural degree. -/
def SmallDegree (d : ℕ) (p : ℤ[X]) : Prop :=
  ∀ i : ℕ, d ≤ 2 * i → p.coeff i = 0

theorem smallDegree_natDegree_le {d : ℕ} {p : ℤ[X]} (hp : SmallDegree d p) :
    p.natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  exact hp i (by omega)

/-- The standard Kazhdan--Lusztig axioms on every interval of a finite ranked flat lattice.
`χ a c` is its independently defined interval characteristic polynomial.
Reflection is at the interval rank, representing `t^d p(t⁻¹)` under the degree bound. -/
structure IsKLFamily (rank : L → ℕ) (χ P : L → L → ℤ[X]) : Prop where
  diagonal : ∀ a, P a a = 1
  small : ∀ a b, a < b → SmallDegree (rank b - rank a) (P a b)
  recurrence : ∀ a b, a ≤ b →
    Polynomial.reflect (rank b - rank a) (P a b) =
      ∑ c ∈ interval a b, χ a c * P c b

/-- Low-degree polynomials are uniquely determined by the skew-reflection equation. -/
theorem small_reflection_unique {d : ℕ} {p q : ℤ[X]}
    (hp : SmallDegree d p) (hq : SmallDegree d q)
    (h : Polynomial.reflect d p - p = Polynomial.reflect d q - q) : p = q := by
  ext i
  by_cases hi : d ≤ 2 * i
  · rw [hp i hi, hq i hi]
  have hid : i ≤ d := by omega
  have hdi : d ≤ 2 * (d - i) := by omega
  have hc := congrArg (fun f : ℤ[X] => f.coeff i) h
  simp only [Polynomial.coeff_sub, Polynomial.coeff_reflect,
    Polynomial.revAt_le hid, hp (d-i) hdi, hq (d-i) hdi, zero_sub] at hc
  exact neg_injective hc

/-- The full interval recurrence and strict degree bound admit at most one family
on comparable pairs. This theorem does not assume the proposed family formula. -/
theorem klFamily_unique [DecidableEq L] {rank : L → ℕ} {χ P Q : L → L → ℤ[X]}
    (hrank : StrictMono rank) (hχ : ∀ a, χ a a = 1)
    (hp : IsKLFamily rank χ P) (hq : IsKLFamily rank χ Q) :
    ∀ a b, a ≤ b → P a b = Q a b := by
  have main : ∀ n : ℕ, ∀ a b : L, rank b - rank a = n →
      a ≤ b → P a b = Q a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b hn hab
      by_cases he : a = b
      · subst b
        rw [hp.diagonal, hq.diagonal]
      have hab' : a < b := lt_of_le_of_ne hab he
      have hmem : a ∈ interval a b := (mem_interval a b a).mpr ⟨le_rfl, hab⟩
      have hrest :
          (∑ c ∈ (interval a b).erase a, χ a c * P c b) =
          ∑ c ∈ (interval a b).erase a, χ a c * Q c b := by
        apply Finset.sum_congr rfl
        intro c hc
        obtain ⟨hca, hc⟩ := Finset.mem_erase.mp hc
        obtain ⟨hac, hcb⟩ := (mem_interval a b c).mp hc
        have hac' : a < c := lt_of_le_of_ne hac (Ne.symm hca)
        have hrc : rank a < rank c := hrank hac'
        have hcb' : rank c ≤ rank b := hrank.monotone hcb
        have hn' : rank b - rank c < n := by omega
        rw [ih (rank b - rank c) hn' c b rfl hcb]
      have hP := hp.recurrence a b hab
      have hQ := hq.recurrence a b hab
      rw [← Finset.sum_erase_add _ _ hmem, hχ, one_mul] at hP hQ
      apply small_reflection_unique (hp.small a b hab') (hq.small a b hab')
      rw [hP, hQ, hrest]
      abel
  intro a b hab
  exact main (rank b - rank a) a b rfl hab

/-- Existence of one certified family gives a unique polynomial at every genuine interval.
No uniqueness is asserted for values at incomparable pairs, which the axioms do not constrain. -/
theorem klValue_existsUnique [DecidableEq L] {rank : L → ℕ} {χ P : L → L → ℤ[X]}
    (hrank : StrictMono rank) (hχ : ∀ a, χ a a = 1)
    (hp : IsKLFamily rank χ P) (a b : L) (hab : a ≤ b) :
    ∃! p : ℤ[X], ∃ Q : L → L → ℤ[X], IsKLFamily rank χ Q ∧ Q a b = p := by
  refine ⟨P a b, ⟨P, hp, rfl⟩, ?_⟩
  intro p hex
  obtain ⟨Q, hQ, rfl⟩ := hex
  exact klFamily_unique hrank hχ hQ hp a b hab

section Transport

variable {K : Type*} [Fintype K] [PartialOrder K]
  [DecidableRel ((· ≤ ·) : K → K → Prop)]

/-- Reindex a two-endpoint invariant through an order isomorphism. -/
def transportPair {V : Type*} (e : L ≃o K) (f : L → L → V) (a b : K) : V :=
  f (e.symm a) (e.symm b)

theorem interval_sum_transport {V : Type*} [AddCommMonoid V]
    (e : L ≃o K) (a b : K) (f : L → V) :
    (∑ c ∈ interval a b, f (e.symm c)) =
      ∑ c ∈ interval (e.symm a) (e.symm b), f c := by
  simp only [interval, Finset.sum_filter]
  apply Fintype.sum_equiv e.symm.toEquiv
  intro c
  simp

/-- Transport the complete KL characterization, not just its final polynomial value. -/
theorem IsKLFamily.transport {rank : L → ℕ} {χ P : L → L → ℤ[X]}
    (hp : IsKLFamily rank χ P) (e : L ≃o K) :
    IsKLFamily (fun a => rank (e.symm a)) (transportPair e χ) (transportPair e P) where
  diagonal a := hp.diagonal (e.symm a)
  small a b hab := hp.small (e.symm a) (e.symm b) (e.symm.strictMono hab)
  recurrence a b hab := by
    simp only [transportPair]
    rw [interval_sum_transport e a b (fun c => χ (e.symm a) c * P c (e.symm b))]
    exact hp.recurrence (e.symm a) (e.symm b) (e.symm.monotone hab)

end Transport

end Conjecture574
