import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Tactic

noncomputable section
namespace AlternatingHalfspaces
open scoped InnerProductSpace Topology
open Filter
abbrev E := EuclideanSpace ℝ (Fin 2)
def vec (x y : ℝ) : E := !₂[x, y]
def A : Set E := {z | 0 ≤ z 1}
def B : Set E := {z | z 0 ≤ z 1}
def pA (z : E) : E := vec (z 0) (max 0 (z 1))
def pB (z : E) : E :=
  if z 0 ≤ z 1 then z else vec ((z 0 + z 1)/2) ((z 0 + z 1)/2)
def start : E := vec 2 (-1)
def first : E := vec 2 0
def limitPoint : E := vec 1 1
def nearer : E := vec (1/2) (1/2)
def Nearest (K : Set E) (x p : E) : Prop := p ∈ K ∧ ∀ z ∈ K, dist x p ≤ dist x z

theorem sq_dist (x z : E) :
    (dist x z)^2 = (x 0 - z 0)^2 + (x 1 - z 1)^2 := by
  rw [dist_eq_norm, PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem A_closed : IsClosed A := by
  exact isClosed_le continuous_const (PiLp.proj (p := 2) (β := fun _ : Fin 2 => ℝ) (𝕜 := ℝ) 1).continuous
theorem B_closed : IsClosed B := by
  exact isClosed_le (PiLp.proj (p := 2) (β := fun _ : Fin 2 => ℝ) (𝕜 := ℝ) 0).continuous (PiLp.proj (p := 2) (β := fun _ : Fin 2 => ℝ) (𝕜 := ℝ) 1).continuous
theorem A_convex : Convex ℝ A := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x 1 + b * y 1
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
theorem B_convex : Convex ℝ B := by
  intro x hx y hy a b ha hb hab
  change a * x 0 + b * y 0 ≤ a * x 1 + b * y 1
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

theorem pA_nearest (x : E) : Nearest A x (pA x) := by
  constructor
  · simp [A, pA, vec]
  · intro z hz
    apply nonneg_le_nonneg_of_sq_le_sq (dist_nonneg)
    rw [← pow_two, ← pow_two, sq_dist, sq_dist]
    simp only [pA, vec]
    change (x 0 - x 0)^2 + (x 1 - max 0 (x 1))^2 ≤ (x 0 - z 0)^2 + (x 1 - z 1)^2
    change 0 ≤ z 1 at hz
    by_cases h : 0 ≤ x 1
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (x 0 - z 0), sq_nonneg (x 1 - z 1)]
    · rw [max_eq_left (le_of_not_ge h)]
      nlinarith [sq_nonneg (x 0 - z 0), sq_nonneg (z 1), mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hz]

theorem pB_nearest (x : E) : Nearest B x (pB x) := by
  by_cases h : x 0 ≤ x 1
  · simp only [pB, if_pos h]
    exact ⟨h, fun _ _ => by simpa using dist_nonneg⟩
  · constructor
    · simp [B, pB, h, vec]
    · intro z hz
      apply nonneg_le_nonneg_of_sq_le_sq (dist_nonneg)
      rw [← pow_two, ← pow_two, sq_dist, sq_dist]
      simp [pB, h, vec]
      change z 0 ≤ z 1 at hz
      have hm : 0 ≤ (x 0 - x 1) * (z 1 - z 0) :=
        mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (sub_nonneg.mpr hz)
      nlinarith [sq_nonneg (z 0 - (x 0 + x 1)/2),
        sq_nonneg (z 1 - (x 0 + x 1)/2)]

theorem projection_steps : pA start = first ∧ pB first = limitPoint ∧
    pA limitPoint = limitPoint ∧ pB limitPoint = limitPoint := by
  norm_num [pA, pB, start, first, limitPoint, vec]

def iterates : ℕ → E
  | 0 => start
  | n+1 => pB (pA (iterates n))
theorem all_iterates (n : ℕ) : iterates (n+1) = limitPoint := by
  induction n with
  | zero => exact congrArg pB projection_steps.1 |>.trans projection_steps.2.1
  | succ n ih =>
      change pB (pA (iterates (n+1))) = limitPoint
      rw [ih, projection_steps.2.2.1, projection_steps.2.2.2]

theorem strong_limit : Tendsto iterates atTop (𝓝 limitPoint) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact (all_iterates k).symm

def WeaklyConverges (u : ℕ → E) (p : E) : Prop :=
  ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f p))
theorem weak_limit : WeaklyConverges iterates limitPoint := by
  intro f
  exact f.continuous.continuousAt.tendsto.comp strong_limit

theorem weak_limit_unique (p : E) (hp : WeaklyConverges iterates p) : p = limitPoint := by
  ext i
  let f : E →L[ℝ] ℝ := PiLp.proj (p := 2) (β := fun _ : Fin 2 => ℝ) i
  exact tendsto_nhds_unique (hp f) (weak_limit f)

theorem intersection_nonempty : (A ∩ B).Nonempty := by
  exact ⟨limitPoint, by norm_num [A, B, limitPoint, vec]⟩
theorem nearer_mem : nearer ∈ A ∩ B := by norm_num [nearer, A, B, vec]
theorem strictly_nearer : dist start nearer < dist start limitPoint := by
  have h1 : (dist start nearer)^2 = 9/2 := by rw [sq_dist]; norm_num [start, nearer, vec]
  have h2 : (dist start limitPoint)^2 = 5 := by rw [sq_dist]; norm_num [start, limitPoint, vec]
  nlinarith [dist_nonneg (x := start) (y := nearer), dist_nonneg (x := start) (y := limitPoint)]

theorem not_nearest : ¬ Nearest (A ∩ B) start limitPoint := by
  intro h
  exact (not_le_of_gt strictly_nearer) (h.2 nearer nearer_mem)

theorem no_nearest_weak_limit :
    ¬ ∃ p, WeaklyConverges iterates p ∧ Nearest (A ∩ B) start p := by
  rintro ⟨p, hp, hn⟩
  rw [weak_limit_unique p hp] at hn
  exact not_nearest hn

def fullOrbit : ℕ → E
  | 0 => start
  | 1 => first
  | _+2 => limitPoint

theorem fullOrbit_recursion (n : ℕ) :
    fullOrbit (n+1) = if n % 2 = 0 then pA (fullOrbit n) else pB (fullOrbit n) := by
  cases n with
  | zero => simpa [fullOrbit] using projection_steps.1.symm
  | succ n =>
      cases n with
      | zero => simpa [fullOrbit] using projection_steps.2.1.symm
      | succ n => simp [fullOrbit, projection_steps.2.2.1, projection_steps.2.2.2]

theorem fullOrbit_strong_limit : Tendsto fullOrbit atTop (𝓝 limitPoint) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp [fullOrbit, Nat.add_comm]

theorem fullOrbit_no_nearest_weak_limit :
    ¬ ∃ p, WeaklyConverges fullOrbit p ∧ Nearest (A ∩ B) start p := by
  rintro ⟨p, hp, hn⟩
  have heq : p = limitPoint := by
    ext i
    let f : E →L[ℝ] ℝ := PiLp.proj (p := 2) (β := fun _ : Fin 2 => ℝ) i
    exact tendsto_nhds_unique (hp f)
      (f.continuous.continuousAt.tendsto.comp fullOrbit_strong_limit)
  rw [heq] at hn
  exact not_nearest hn

theorem counterexample : IsClosed A ∧ IsClosed B ∧ Convex ℝ A ∧ Convex ℝ B ∧
    (A ∩ B).Nonempty ∧ (∀ x, Nearest A x (pA x)) ∧
    (∀ x, Nearest B x (pB x)) ∧ WeaklyConverges iterates limitPoint ∧
    ¬ Nearest (A ∩ B) start limitPoint :=
  ⟨A_closed, B_closed, A_convex, B_convex, intersection_nonempty,
    pA_nearest, pB_nearest, weak_limit, not_nearest⟩
end AlternatingHalfspaces
#print axioms AlternatingHalfspaces.pA_nearest
#print axioms AlternatingHalfspaces.pB_nearest
#print axioms AlternatingHalfspaces.all_iterates
#print axioms AlternatingHalfspaces.strong_limit
#print axioms AlternatingHalfspaces.weak_limit
#print axioms AlternatingHalfspaces.counterexample
#print axioms AlternatingHalfspaces.no_nearest_weak_limit
#print axioms AlternatingHalfspaces.fullOrbit_recursion
#print axioms AlternatingHalfspaces.fullOrbit_no_nearest_weak_limit
