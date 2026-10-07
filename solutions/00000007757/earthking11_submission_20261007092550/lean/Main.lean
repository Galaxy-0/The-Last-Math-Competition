import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.NormNum

namespace TLMC7757

abbrev K := AlgebraicClosure ℚ

noncomputable def f (z : K) : K := z ^ 2
noncomputable def g (z : K) : K := z ^ 4

theorem f_iterate (n : ℕ) (z : K) : (f^[n]) z = z ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [f, pow_succ, pow_mul]

theorem g_iterate (n : ℕ) (z : K) : (g^[n]) z = z ^ (4 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [g, pow_succ, pow_mul]

def order (n : ℕ) : ℕ := 2 ^ (n + 1) - 1

theorem order_pos (n : ℕ) : 0 < order n := by
  have hp : 0 < 2 ^ (n + 1) := pow_pos (by decide) _
  unfold order
  omega

theorem order_strict : StrictMono order := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp : 0 < 2 ^ (n + 1) := pow_pos (by decide) _
  have hpow : 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 := by rw [pow_succ]
  unfold order
  simpa [Nat.succ_eq_add_one, hpow, Nat.add_assoc] using
    (show 2 ^ (n + 1) - 1 < 2 ^ (n + 1) * 2 - 1 by omega)

private noncomputable def witness (n : ℕ) : {z : K // IsPrimitiveRoot z (order n)} := by
  letI : NeZero (order n : ℚ) := ⟨by exact_mod_cast (Nat.ne_of_gt (order_pos n))⟩
  have h : ∃ z : K, IsPrimitiveRoot z (order n) :=
    HasEnoughRootsOfUnity.exists_primitiveRoot K (order n)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

noncomputable def root (n : ℕ) : K := (witness n).1
theorem root_spec (n : ℕ) : IsPrimitiveRoot (root n) (order n) := (witness n).2

theorem root_periodic_f (n : ℕ) : (f^[n+1]) (root n) = root n := by
  rw [f_iterate]
  have hp := (root_spec n).pow_eq_one
  have hm : order n + 1 = 2 ^ (n + 1) := by
    have hpos := order_pos n
    unfold order at hpos ⊢
    omega
  rw [← hm, pow_succ, hp, one_mul]

theorem root_periodic_g (n : ℕ) : (g^[n+1]) (root n) = root n := by
  rw [g_iterate]
  have h : 4 ^ (n + 1) = 2 ^ (n + 1) * 2 ^ (n + 1) := by
    calc
      4 ^ (n + 1) = (2 ^ 2) ^ (n + 1) := by norm_num
      _ = 2 ^ (2 * (n + 1)) := by rw [pow_mul]
      _ = 2 ^ ((n + 1) + (n + 1)) := by congr 1; omega
      _ = 2 ^ (n + 1) * 2 ^ (n + 1) := by rw [pow_add]
  rw [h, pow_mul]
  have hf := root_periodic_f n
  rw [f_iterate] at hf
  rw [hf, hf]

theorem root_injective : Function.Injective root := by
  intro n m h
  have ho : order n = order m := by
    rw [(root_spec n).eq_orderOf, (root_spec m).eq_orderOf, h]
  exact order_strict.injective ho

abbrev P1 := Option K

noncomputable def F : P1 → P1 := Option.map f
noncomputable def G : P1 → P1 := Option.map g

def Periodic (h : P1 → P1) (x : P1) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (h^[n]) x = x

theorem affine_iterate_F (n : ℕ) (z : K) : (F^[n]) (some z) = some ((f^[n]) z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [F, Option.map_some, Function.iterate_succ_apply']

theorem affine_iterate_G (n : ℕ) (z : K) : (G^[n]) (some z) = some ((g^[n]) z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [G, Option.map_some, Function.iterate_succ_apply']

theorem periodic_root_F (n : ℕ) : Periodic F (some (root n)) := by
  refine ⟨n + 1, by omega, ?_⟩
  rw [affine_iterate_F, root_periodic_f]

theorem periodic_root_G (n : ℕ) : Periodic G (some (root n)) := by
  refine ⟨n + 1, by omega, ?_⟩
  rw [affine_iterate_G, root_periodic_g]

theorem commute_affine (z : K) : f (g z) = g (f z) := by
  simp only [f, g]
  rw [← pow_mul, ← pow_mul]

theorem commute_projective : Function.Commute F G := by
  intro x
  change Option.map f (Option.map g x) = Option.map g (Option.map f x)
  rw [Option.map_map, Option.map_map]
  congr 1
  funext z
  exact commute_affine z

theorem distinct : F ≠ G := by
  intro h
  have := congrFun h (some (2 : K))
  norm_num [F, G, f, g] at this

theorem degree_two : (Polynomial.X ^ 2 : Polynomial K).degree = 2 := by simp
theorem degree_four : (Polynomial.X ^ 4 : Polynomial K).degree = 4 := by simp

theorem infinite_common_periodic :
    Set.Infinite {x : P1 | Periodic F x ∧ Periodic G x} := by
  have hi : Function.Injective (fun n : ℕ => some (root n)) := by
    intro n m h
    exact root_injective (Option.some.inj h)
  have hr : Set.Infinite (Set.range (fun n : ℕ => some (root n))) :=
    Set.infinite_range_of_injective hi
  exact hr.mono (by
    rintro x ⟨n, rfl⟩
    exact ⟨periodic_root_F n, periodic_root_G n⟩)

#print axioms infinite_common_periodic

end TLMC7757
