import Mathlib.Data.ENat.Lattice
import Mathlib.Order.Fin.Basic
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

noncomputable section
namespace Dataflow
/-- The fixed control-flow graph: one vertex, one self-loop. -/
def cfg : Quiver Unit where
  Hom _ _ := Unit

lemma one_node : Fintype.card Unit = 1 := rfl
lemma self_loop : Nonempty (cfg.Hom () ()) := ⟨()⟩

/-- A single fixed complete information lattice. -/
abbrev State := Unit → ℕ∞
def transfer : ℕ∞ →o ℕ∞ where
  toFun x := x + 1
  monotone' _ _ h := add_le_add_right h 1

/-- Updating the sole incoming edge on the sole vertex. -/
def globalStep (s : State) : State := fun _ => transfer (s ())
def orbit (r : ℕ) : State := (globalStep^[r]) ⊥

lemma global_monotone : Monotone globalStep := by
  intro s t h u
  exact transfer.monotone (h ())

lemma orbit_value (r : ℕ) (u : Unit) : orbit r u = (r : ℕ∞) := by
  induction r generalizing u with
  | zero => simp [orbit]
  | succ r ih =>
    simp only [orbit, Function.iterate_succ_apply']
    change orbit r () + 1 = ((r+1 : ℕ) : ℕ∞)
    rw [ih ()]
    simp [Nat.cast_add]

lemma top_fixed : transfer ⊤ = ⊤ := by simp [transfer]

lemma unique_fixed (x : ℕ∞) : transfer x = x → x = ⊤ := by
  refine ENat.recTopCoe ?_ (fun n => ?_) x
  · intro _; rfl
  · intro h
    have hh : ((n+1 : ℕ) : ℕ∞) = n := by simpa [transfer, Nat.cast_add] using h
    have := ENat.coe_inj.mp hh
    omega

theorem never_finite_stabilization (r : ℕ) : globalStep (orbit r) ≠ orbit r := by
  intro h
  have hh := congrFun h ()
  have hn : ((r+1 : ℕ) : ℕ∞) = r := by
    simpa [globalStep, transfer, orbit_value, Nat.cast_add] using hh
  have := ENat.coe_inj.mp hn
  omega

/-- Finite chain truncations: the actual ordered domain is Fin (m+1). -/
def finiteTransfer (m : ℕ) : Fin (m+1) →o Fin (m+1) where
  toFun x := ⟨min (x.val+1) m, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  monotone' _ _ h := min_le_min (Nat.add_le_add_right h 1) (le_refl m)

abbrev FiniteState (m : ℕ) := Unit → Fin (m+1)
def finiteStep (m : ℕ) (s : FiniteState m) : FiniteState m :=
  fun _ => finiteTransfer m (s ())
def finiteOrbit (m r : ℕ) : FiniteState m := ((finiteStep m)^[r]) ⊥

lemma finite_orbit_value (m r : ℕ) (u : Unit) : (finiteOrbit m r u).val = min r m := by
  induction r generalizing u with
  | zero => simp [finiteOrbit, Fin.bot_eq_zero]
  | succ r ih =>
    simp only [finiteOrbit, Function.iterate_succ_apply', finiteStep]
    change min ((finiteOrbit m r ()).val + 1) m = min (r+1) m
    rw [ih]
    omega

lemma finite_stable_iff (m r : ℕ) : finiteStep m (finiteOrbit m r) = finiteOrbit m r ↔ m ≤ r := by
  constructor
  · intro h
    have hh := congrArg Fin.val (congrFun h ())
    change min ((finiteOrbit m r ()).val+1) m = (finiteOrbit m r ()).val at hh
    rw [finite_orbit_value] at hh
    omega
  · intro h
    funext u
    apply Fin.ext
    change min ((finiteOrbit m r ()).val+1) m = (finiteOrbit m r u).val
    simp only [finite_orbit_value]
    omega

theorem no_uniform_node_only_bound : ¬ ∃ C : ℕ, ∀ m : ℕ,
    ∃ r ≤ C * Fintype.card Unit, finiteStep m (finiteOrbit m r) = finiteOrbit m r := by
  rintro ⟨C, h⟩
  obtain ⟨r, hr, hs⟩ := h (C+1)
  have hm := (finite_stable_iff (C+1) r).mp hs
  simp only [one_node, mul_one] at hr
  omega

end Dataflow
#print axioms Dataflow.cfg
#print axioms Dataflow.global_monotone
#print axioms Dataflow.orbit_value
#print axioms Dataflow.unique_fixed
#print axioms Dataflow.never_finite_stabilization
#print axioms Dataflow.finite_orbit_value
#print axioms Dataflow.finite_stable_iff
#print axioms Dataflow.no_uniform_node_only_bound
