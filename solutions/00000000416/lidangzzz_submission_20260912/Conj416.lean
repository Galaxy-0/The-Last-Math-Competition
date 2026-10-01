/-
  TLMC #416 DISPROOF (standalone)
-/

import Mathlib

namespace TLMC416

/-! ### #416: evacuation orbits on two-row rectangular tableaux -/

/-- Standard Young tableaux of shape `(n, n)`: fillings of the `n × n`
    diagram with the values `0, …, n² − 1`, each exactly once, strictly
    increasing along rows and columns. -/
def sytNN (n : ℕ) : Finset (Fin n → Fin n → Fin (n * n)) :=
  Finset.univ.filter fun T =>
    (∀ i : Fin n, ∀ j : Fin n, ∀ (hj : (j.val + 1 : ℕ) < n),
        (T i ⟨j.val + 1, hj⟩).val > (T i j).val) ∧
    (∀ i : Fin n, ∀ j : Fin n, ∀ (hi : (i.val + 1 : ℕ) < n),
        (T ⟨i.val + 1, hi⟩ j).val > (T i j).val) ∧
    (Finset.univ.image fun p : Fin n × Fin n => T p.1 p.2) = Finset.univ

/-- The evacuation operator on rectangular shapes: 180° rotation of the
    diagram with entrywise complement (Schützenberger). -/
def evNN {n : ℕ} (T : Fin n → Fin n → Fin (n * n)) : Fin n → Fin n → Fin (n * n) :=
  fun i j => ⟨n * n - 1 - (T i.rev j.rev).val, by
    have h := (T i.rev j.rev).isLt
    omega⟩

/-- Evacuation is an involution. -/
theorem evNN_involutive {n : ℕ} (T : Fin n → Fin n → Fin (n * n)) :
    evNN (evNN T) = T := by
  funext i j
  have h1 : i.rev.rev = i := Fin.rev_rev i
  have h2 : j.rev.rev = j := Fin.rev_rev j
  simp only [evNN, h1, h2]
  apply Fin.ext
  show n * n - 1 - (n * n - 1 - (T i j).val) = (T i j).val
  have h3 := (T i j).isLt
  omega

/-- The Fibonacci numbers (indexed `F₀ = 0`, `F₁ = 1`). -/
def Fb : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => Fb n + Fb (n + 1)

set_option maxRecDepth 1000000 in
/-- At `n = 2` there are exactly two standard tableaux of shape `(2,2)`
    and both are fixed by evacuation, so there are no orbits of
    length exactly two (kernel-computed). -/
theorem tlm416_facts :
    (sytNN 2).card = 2 ∧
      (∀ T ∈ sytNN 2, evNN T = T) ∧
      ((sytNN 2).filter fun T => evNN T ≠ T).card = 0 := by
  constructor <;> decide

set_option maxRecDepth 1000000 in
/-- **TLMC #416 is false** (its third clause): the number of orbits of
    length exactly `2` at `n = 2` is `0`, not `F_{n-1} = F₁ = 1`. -/
theorem tlm416_false :
    ((sytNN 2).filter fun T => evNN T ≠ T).card / 2 ≠ Fb (2 - 1) := by
  decide


end TLMC416
