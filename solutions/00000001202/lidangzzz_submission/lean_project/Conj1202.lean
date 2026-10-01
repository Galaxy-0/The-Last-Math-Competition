/-
  TLMC #1202 DISPROOF (standalone)
-/

import Mathlib

namespace TLMC1202

/-! ### #1202: the octal game 0.07 -/

/-- The least natural number not contained in `opts` (upward scan with
    enough fuel; the fuel bound suffices by the pigeonhole principle,
    see `mexL_spec`). -/
def mexScan (opts : List ℕ) : ℕ → ℕ → ℕ
  | 0, cur => cur
  | fuel + 1, cur => if cur ∈ opts then mexScan opts fuel (cur + 1) else cur

def mexL (opts : List ℕ) : ℕ := mexScan opts (opts.length + 1) 0

theorem mexScan_spec : ∀ (fuel : ℕ) (opts : List ℕ) (cur : ℕ),
    (∀ x < cur, x ∈ opts) →
    ((mexScan opts fuel cur ∉ opts ∧
        ∀ x, cur ≤ x → x < mexScan opts fuel cur → x ∈ opts) ∨
      (mexScan opts fuel cur = cur + fuel ∧
        ∀ x < cur + fuel, x ∈ opts)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro opts cur h
      exact Or.inr ⟨rfl, h⟩
  | succ fuel ih =>
      intro opts cur h
      by_cases hc : cur ∈ opts
      · rw [mexScan, if_pos hc]
        rcases ih opts (cur + 1) (fun x hx => by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx' | hx'
            · exact h x hx'
            · exact hx' ▸ hc) with h1 | h2
        · refine Or.inl ⟨h1.1, fun x hx1 hx2 => ?_⟩
          rcases Nat.eq_or_lt_of_le hx1 with hx3 | hx3
          · exact hx3 ▸ hc
          · exact h1.2 x hx3 hx2
        · exact Or.inr ⟨h2.1.trans (by omega), fun x hx => h2.2 x (by omega)⟩
      · rw [mexScan, if_neg hc]
        exact Or.inl ⟨hc, fun x h1 h2 => by omega⟩

/-- `mexL` really is the least excluded value. -/
theorem mexL_spec (opts : List ℕ) :
    mexL opts ∉ opts ∧ ∀ m, m < mexL opts → m ∈ opts := by
  rcases mexScan_spec (opts.length + 1) opts 0 (fun _ h => absurd h (Nat.not_lt_zero _))
    with h1 | h2
  · exact ⟨h1.1, fun m hm => h1.2 m (Nat.zero_le m) hm⟩
  · exfalso
    have hsub : (List.range (opts.length + 1)).toFinset ⊆ opts.toFinset := by
      intro x hx
      have hx' : x < 0 + (opts.length + 1) := by
        simpa using List.mem_range.1 (List.mem_toFinset.1 hx)
      exact List.mem_toFinset.2 (h2.2 x hx')
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_range, Finset.card_range] at hcard
    have h3 := List.toFinset_card_le opts
    omega

/-- The SG sequence of the octal game `0.07`, computed as growing lists:
    `g07L m` holds the values `g(0), …, g(m)`.  From a heap of size
    `n + 2` one removes two tokens, leaving heaps of sizes `i` and
    `n - i` for any `0 ≤ i ≤ n`; heaps of sizes `0` and `1` have no move,
    so `g(0) = g(1) = 0`. -/
def g07L : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0, 0]
  | n + 2 => g07L (n + 1) ++ [mexL ((List.range (n + 1)).map fun i =>
      (g07L (n + 1)).getD i 0 ^^^ (g07L (n + 1)).getD (n - i) 0)]

/-- The SG function of the octal game `0.07`. -/
def g07 (n : ℕ) : ℕ := (g07L n).getD n 0

theorem g07L_length : ∀ m, (g07L m).length = m + 1 := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases m with _ | m'
      · rfl
      · show (g07L (m' + 2)).length = m' + 2 + 1
        rw [g07L, List.length_append, ih, List.length_singleton]

theorem g07L_get : ∀ (m i : ℕ), i ≤ m → (g07L m).getD i 0 = g07 i := by
  intro m
  induction m with
  | zero =>
      intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0]
      rfl
  | succ m ih =>
      rcases m with _ | m'
      · intro i hi
        rcases i with _ | i
        · rfl
        · rcases i with _ | i
          · rfl
          · omega
      · intro i hi
        have hlen := g07L_length (m' + 1)
        by_cases hlt : i < m' + 2
        · show (g07L (m' + 1) ++ [mexL ((List.range (m' + 1)).map fun i =>
              (g07L (m' + 1)).getD i 0 ^^^ (g07L (m' + 1)).getD (m' - i) 0)]).getD i 0
            = g07 i
          rw [List.getD_append _ _ _ _ (by omega)]
          exact ih i (by omega)
        · have hi2 : i = m' + 2 := by omega
          rw [hi2]
          rfl

/-- The computed function satisfies the SG recursion of the game. -/
theorem g07_rec : ∀ n, g07 (n + 2) =
    mexL ((List.range (n + 1)).map fun i => g07 i ^^^ g07 (n - i)) := by
  intro n
  have hlen := g07L_length (n + 1)
  show (g07L (n + 2)).getD (n + 2) 0 = _
  have hle : (g07L (n + 1)).length ≤ n + 2 := by rw [hlen]
  have hsub : n + 2 - (n + 1 + 1) = 0 := by omega
  rw [g07L, List.getD_append_right _ _ _ _ hle, hlen, hsub, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi1 : i ≤ n + 1 := by
    simp only [List.mem_range] at hi
    omega
  rw [g07L_get (n + 1) i hi1, g07L_get (n + 1) (n - i) (by omega)]

/-- The first seventeen SG values (kernel-computed). -/
theorem g07_values :
    (List.range 17).map g07 = [0, 0, 1, 1, 2, 0, 3, 1, 1, 0, 3, 3, 2, 2, 4, 0, 5] := by
  decide

/-- **TLMC #1202 is false**: `g(4) = 2` but `g(4 + 12) = 5`, so the claimed
    law `g(n + 12) = g(n)` for all `n ≥ 4` fails at `n = 4`. -/
theorem tlm1202_false : ¬ ∀ n, 4 ≤ n → g07 (n + 12) = g07 n := by
  intro h
  have h4 : g07 16 = g07 4 := h 4 (by omega)
  have e4 : g07 4 = 2 := by decide
  have e16 : g07 16 = 5 := by decide
  rw [e16, e4] at h4
  exact absurd h4 (by decide)


end TLMC1202
