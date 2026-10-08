import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

open scoped Interval
open Finset
namespace SignatureCounterexample
abbrev Time := Set.Icc (0 : ℝ) 1
abbrev Path := C(Time, ℝ)
def initial (p : Path) : ℝ := p ⟨0, by constructor <;> norm_num⟩
def constantPath (a : ℝ) : Path := ContinuousMap.const Time a

theorem initial_lipschitz : LipschitzWith 1 initial := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa [initial] using ContinuousMap.dist_apply_le_dist (f := p) (g := q)
    (⟨0, by constructor <;> norm_num⟩ : Time)

-- Standard one-dimensional smooth-path signature recursion.
noncomputable def level (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n+1, t => ∫ s in (0 : ℝ)..t, level g n s * deriv g s

theorem constant_level (a t : ℝ) (n : ℕ) :
    level (fun _ => a) n t = if n = 0 then 1 else 0 := by
  cases n with
  | zero => rfl
  | succ n => simp [level, deriv_const]

noncomputable def linearSignature (N : ℕ) (c : Fin (N+1) → ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ i, c i * level g i.val 1

theorem constant_signature (N : ℕ) (c : Fin (N+1) → ℝ) (a : ℝ) :
    linearSignature N c (fun _ => a) = linearSignature N c (fun _ => (0 : ℝ)) := by
  unfold linearSignature
  apply sum_congr rfl
  intro i hi
  rw [constant_level, constant_level]

theorem pair_error (N : ℕ) (c : Fin (N+1) → ℝ) (E : ℝ)
    (h0 : |initial (constantPath 0) - linearSignature N c (fun _ => 0)| ≤ E)
    (h1 : |initial (constantPath 1) - linearSignature N c (fun _ => 1)| ≤ E) :
    1/2 ≤ E := by
  rw [constant_signature N c 1] at h1
  change |0 - linearSignature N c (fun _ => 0)| ≤ E at h0
  change |1 - linearSignature N c (fun _ => 0)| ≤ E at h1
  have ha := (abs_le.mp h0).1
  have hb := (abs_le.mp h1).2
  linarith

theorem no_uniform_bound (N : ℕ) (c : Fin (N+1) → ℝ) (E : ℝ) :
    ¬ ∀ a : ℝ, |initial (constantPath a) - linearSignature N c (fun _ => a)| ≤ E := by
  intro h
  let b := linearSignature N c (fun _ => 0)
  have ha := h (b + |E| + 1)
  rw [constant_signature] at ha
  change |(b + |E| + 1) - b| ≤ E at ha
  have hu := (abs_le.mp ha).2
  have := le_abs_self E
  linarith

theorem no_decaying_rate (C : ℝ) (hC : 0 ≤ C) :
    ¬ ∀ N : ℕ, 0 < N → ∃ c : Fin (N+1) → ℝ,
      (|initial (constantPath 0) - linearSignature N c (fun _ => 0)| ≤ C / Real.sqrt N) ∧
      (|initial (constantPath 1) - linearSignature N c (fun _ => 1)| ≤ C / Real.sqrt N) := by
  intro h
  obtain ⟨N, hN⟩ := exists_nat_gt ((2*C+1)^2)
  have hNp : 0 < (N : ℝ) := lt_of_le_of_lt (sq_nonneg _) hN
  have hnat : 0 < N := by exact_mod_cast hNp
  obtain ⟨c, hc0, hc1⟩ := h N hnat
  have he := pair_error N c (C / Real.sqrt N) hc0 hc1
  have hs : Real.sqrt (N : ℝ)^2 = N := Real.sq_sqrt (le_of_lt hNp)
  have hsp : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNp
  have hsmall : C / Real.sqrt (N : ℝ) < 1/2 := by
    apply (div_lt_iff₀ hsp).2
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  linarith

#print axioms initial_lipschitz
#print axioms constant_level
#print axioms constant_signature
#print axioms pair_error
#print axioms no_uniform_bound
#print axioms no_decaying_rate
end SignatureCounterexample
