import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! An unbounded family of 3-regular graphs with only one prime cycle length. -/

namespace TLMC57

open Filter
open scoped Topology

def graph (m : ℕ) : SimpleGraph (Fin m × Fin 4) where
  Adj u v := u.1 = v.1 ∧ u.2 ≠ v.2
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.2 rfl⟩

instance (m : ℕ) : DecidableRel (graph m).Adj :=
  fun u v => inferInstanceAs (Decidable (u.1 = v.1 ∧ u.2 ≠ v.2))

def neighborsEquiv {m : ℕ} (v : Fin m × Fin 4) :
    (graph m).neighborSet v ≃ {j : Fin 4 // j ≠ v.2} where
  toFun w := ⟨w.val.2, w.property.2.symm⟩
  invFun j := ⟨(v.1, j.val), ⟨rfl, j.property.symm⟩⟩
  left_inv w := by
    apply Subtype.ext
    exact Prod.ext w.property.1 rfl
  right_inv j := rfl

theorem degree_three {m : ℕ} (v : Fin m × Fin 4) : (graph m).degree v = 3 := by
  have hcard : Fintype.card {j : Fin 4 // j ≠ v.2} = 3 := by
    rcases v with ⟨i, j⟩
    change Fintype.card {k : Fin 4 // k ≠ j} = 3
    fin_cases j <;> decide
  calc
    (graph m).degree v = Fintype.card ((graph m).neighborSet v) :=
      ((graph m).card_neighborSet_eq_degree v).symm
    _ = Fintype.card {j : Fin 4 // j ≠ v.2} := Fintype.card_congr (neighborsEquiv v)
    _ = 3 := hcard

theorem walk_stays_in_component {m : ℕ} {u v : Fin m × Fin 4}
    (w : (graph m).Walk u v) (n : ℕ) : (w.getVert n).1 = u.1 := by
  induction w generalizing n with
  | nil => rfl
  | @cons a b c h w ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [SimpleGraph.Walk.getVert_cons_succ]
      exact (ih n).trans h.1.symm

theorem cycle_length_le_four {m : ℕ} {u : Fin m × Fin 4}
    (w : (graph m).Walk u u) (hc : w.IsCycle) : w.length ≤ 4 := by
  let f : Fin w.length → Fin 4 := fun i => (w.getVert i.val).2
  have hf : Function.Injective f := by
    intro i j hij
    have hv : w.getVert i.val = w.getVert j.val := by
      apply Prod.ext
      · exact (walk_stays_in_component w i.val).trans
          (walk_stays_in_component w j.val).symm
      · exact hij
    have heq := hc.getVert_injOn' (by change i.val ≤ w.length - 1; omega)
      (by change j.val ≤ w.length - 1; omega) hv
    exact Fin.ext heq
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

theorem prime_cycle_length_is_three {m : ℕ} {u : Fin m × Fin 4}
    (w : (graph m).Walk u u) (hc : w.IsCycle) (hp : w.length.Prime) : w.length = 3 := by
  have hlo := hc.three_le_length
  have hhi := cycle_length_le_four w hc
  have heq : w.length = 3 ∨ w.length = 4 := by omega
  rcases heq with h | h
  · exact h
  · rw [h] at hp
    exact False.elim ((by decide : ¬ Nat.Prime 4) hp)

theorem no_two_distinct_prime_cycle_lengths {m : ℕ} {u v : Fin m × Fin 4}
    (w : (graph m).Walk u u) (z : (graph m).Walk v v)
    (hw : w.IsCycle) (hz : z.IsCycle) (hpw : w.length.Prime) (hpz : z.length.Prime) :
    w.length = z.length := by
  rw [prime_cycle_length_is_three w hw hpw, prime_cycle_length_is_three z hz hpz]

theorem arbitrarily_large_counterexamples (N : ℕ) :
    ∃ m : ℕ, N < Fintype.card (Fin m × Fin 4) ∧
      (∀ v : Fin m × Fin 4, (graph m).degree v = 3) ∧
      (∀ (u : Fin m × Fin 4) (w : (graph m).Walk u u),
        w.IsCycle → w.length.Prime → w.length = 3) := by
  refine ⟨N + 1, ?_, degree_three, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  · intro u w hc hp
    exact prime_cycle_length_is_three w hc hp

#print axioms arbitrarily_large_counterexamples
#print axioms no_two_distinct_prime_cycle_lengths

theorem prime_length_set_card_le_one {m : ℕ} (L : Finset ℕ)
    (hL : ∀ k ∈ L, k.Prime ∧ ∃ (u : Fin m × Fin 4) (w : (graph m).Walk u u),
      w.IsCycle ∧ w.length = k) : L.card ≤ 1 := by
  have hsub : L ⊆ {3} := by
    intro k hk
    rcases hL k hk with ⟨hp, u, w, hc, heq⟩
    have hthree := prime_cycle_length_is_three w hc (heq.symm ▸ hp)
    simpa using heq.symm.trans hthree
  simpa using Finset.card_le_card hsub

theorem logarithmic_ratio_tends_to_infinity :
    Tendsto (fun m : ℕ => Real.log (4 * (m : ℝ)) /
      Real.log (Real.log (4 * (m : ℝ)))) atTop atTop := by
  have hsize : Tendsto (fun m : ℕ => 4 * (m : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hsize
  have hsmall : Tendsto (fun m : ℕ => Real.log (Real.log (4 * (m : ℝ))) /
      Real.log (4 * (m : ℝ))) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlog
  have hpositive : ∀ᶠ m : ℕ in atTop,
      0 < Real.log (Real.log (4 * (m : ℝ))) / Real.log (4 * (m : ℝ)) := by
    filter_upwards [hlog.eventually (eventually_gt_atTop (1 : ℝ))] with m hm
    dsimp [Function.comp_def] at hm
    exact div_pos (Real.log_pos hm) (by linarith)
  have hwithin : Tendsto (fun m : ℕ => Real.log (Real.log (4 * (m : ℝ))) /
      Real.log (4 * (m : ℝ))) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsmall, hpositive⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun m : ℕ => (Real.log (Real.log (4 * (m : ℝ))) /
    Real.log (4 * (m : ℝ)))⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

/-- For every proposed positive constant and threshold, an actual cubic graph
    beyond the threshold defeats the lower bound on distinct prime lengths. -/
theorem defeats_every_uniform_bound (a : ℝ) (ha : 0 < a) (N₀ : ℕ) :
    ∃ m : ℕ, N₀ ≤ Fintype.card (Fin m × Fin 4) ∧
      (∀ v : Fin m × Fin 4, (graph m).degree v = 3) ∧
      (∀ L : Finset ℕ,
        (∀ k ∈ L, k.Prime ∧ ∃ (u : Fin m × Fin 4) (w : (graph m).Walk u u),
          w.IsCycle ∧ w.length = k) →
        (L.card : ℝ) < a * (Real.log (Fintype.card (Fin m × Fin 4)) /
          Real.log (Real.log (Fintype.card (Fin m × Fin 4))))) := by
  have hevent : ∀ᶠ m : ℕ in atTop, N₀ ≤ m ∧
      1 / a < Real.log (4 * (m : ℝ)) / Real.log (Real.log (4 * (m : ℝ))) :=
    (eventually_ge_atTop N₀).and
      (logarithmic_ratio_tends_to_infinity.eventually (eventually_gt_atTop (1 / a)))
  obtain ⟨m, hm, hratio⟩ := hevent.exists
  refine ⟨m, ?_, degree_three, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  · intro L hL
    have hc : (L.card : ℝ) ≤ 1 := by exact_mod_cast prime_length_set_card_le_one L hL
    have hgt : 1 < a * (Real.log (4 * (m : ℝ)) /
        Real.log (Real.log (4 * (m : ℝ)))) := by
      have h := (div_lt_iff₀ ha).mp hratio
      nlinarith
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
      mul_comm (m : ℝ) 4] using hc.trans_lt hgt

#print axioms defeats_every_uniform_bound

end TLMC57
