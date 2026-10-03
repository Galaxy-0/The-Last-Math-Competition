import Std

namespace Conjecture4396
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- A finite simple undirected graph on its actual vertex set. -/
structure Graph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symmetric : ∀ i j, adj i j = adj j i
  loopless : ∀ i, adj i i = false

def edgeCount {n : Nat} (G : Graph n) : Nat :=
  ((List.finRange n).flatMap fun i =>
    (List.finRange n).filter fun j => decide (i.val < j.val) && G.adj i j).length

def Hom {m n : Nat} (H : Graph m) (G : Graph n) (f : Fin m → Fin n) : Prop :=
  ∀ i j, H.adj i j = true → G.adj (f i) (f j) = true
instance {m n : Nat} (H : Graph m) (G : Graph n) (f : Fin m → Fin n) :
    Decidable (Hom H G f) := by unfold Hom; infer_instance

def homCount {m n : Nat} (H : Graph m) (G : Graph n)
    (maps : List (Fin m → Fin n)) : Nat :=
  (maps.filter fun f => decide (Hom H G f)).length

/-- Exact finite homomorphism-density inequality after multiplying positive
    denominators. Maps must enumerate ALL vertex maps, exactly once. -/
def Sidorenko {m : Nat} (H : Graph m) : Prop :=
  ∀ n : Nat, 0 < n → ∀ G : Graph n,
  ∀ maps : List (Fin m → Fin n), maps.Nodup → (∀ f, f ∈ maps) →
    (2 * edgeCount G) ^ edgeCount H * n ^ m ≤
      homCount H G maps * n ^ (2 * edgeCount H)

/-- The cycle on 2r vertices together with all opposite-vertex edges. -/
def mobiusAdj (r : Nat) (i j : Fin (2*r)) : Bool :=
  ((i.val + 1) % (2*r) == j.val) ||
  ((j.val + 1) % (2*r) == i.val) ||
  ((i.val + r) % (2*r) == j.val)

def M8 : Graph 8 where
  adj := mobiusAdj 4
  symmetric := by decide
  loopless := by decide

def K2 : Graph 2 where
  adj := fun i j => i != j
  symmetric := by decide
  loopless := by decide

theorem actual_edge_counts : edgeCount M8 = 12 ∧ edgeCount K2 = 1 := by decide

/-- This works for every actual map, not just the forthcoming enumeration. -/
theorem no_hom_to_K2 (f : Fin 8 → Fin 2) : ¬ Hom M8 K2 f := by
  intro h
  have h01 := h 0 1 (by decide)
  have h12 := h 1 2 (by decide)
  have h23 := h 2 3 (by decide)
  have h34 := h 3 4 (by decide)
  have h40 := h 4 0 (by decide)
  change (f 0 != f 1) = true at h01
  change (f 1 != f 2) = true at h12
  change (f 2 != f 3) = true at h23
  change (f 3 != f 4) = true at h34
  change (f 4 != f 0) = true at h40
  have two : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  rcases two (f 0) with h0 | h0 <;>
    rcases two (f 1) with h1 | h1 <;>
    rcases two (f 2) with h2 | h2 <;>
    rcases two (f 3) with h3 | h3 <;>
    rcases two (f 4) with h4 | h4 <;>
    simp_all

abbrev Code := Fin 256

def mapOf (c : Code) (i : Fin 8) : Fin 2 :=
  ⟨(c.val / 2^i.val) % 2, Nat.mod_lt _ (by decide)⟩

def codeOf (f : Fin 8 → Fin 2) : Code :=
  ⟨(f 0 |>.val) + 2*(f 1 |>.val) + 4*(f 2 |>.val) + 8*(f 3 |>.val) +
    16*(f 4 |>.val) + 32*(f 5 |>.val) + 64*(f 6 |>.val) + 128*(f 7 |>.val), by
      have h0 := (f 0).isLt
      have h1 := (f 1).isLt
      have h2 := (f 2).isLt
      have h3 := (f 3).isLt
      have h4 := (f 4).isLt
      have h5 := (f 5).isLt
      have h6 := (f 6).isLt
      have h7 := (f 7).isLt
      omega⟩

def table (b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2) (i : Fin 8) : Fin 2 :=
  match i.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3
  | 4 => b4 | 5 => b5 | 6 => b6 | _ => b7

theorem mapOf_codeOf_table : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
    ∀ i : Fin 8,
    mapOf (codeOf (table b0 b1 b2 b3 b4 b5 b6 b7)) i =
      table b0 b1 b2 b3 b4 b5 b6 b7 i := by decide

theorem table_values (f : Fin 8 → Fin 2) :
    table (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) = f := by
  funext i
  have h : ∀ i : Fin 8,
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by decide
  rcases h i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem every_map_encoded (f : Fin 8 → Fin 2) : mapOf (codeOf f) = f := by
  have h := funext (mapOf_codeOf_table (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7))
  rw [table_values f] at h
  exact h

theorem codeOf_mapOf : ∀ c : Code, codeOf (mapOf c) = c := by decide

theorem mapOf_injective (a b : Code) (h : mapOf a = mapOf b) : a = b := by
  have h' := congrArg codeOf h
  simpa only [codeOf_mapOf] using h'

def allMaps : List (Fin 8 → Fin 2) := (List.finRange 256).map mapOf

theorem allMaps_complete (f : Fin 8 → Fin 2) : f ∈ allMaps := by
  apply List.mem_map.mpr
  refine ⟨codeOf f, ?_, every_map_encoded f⟩
  have all : ∀ c : Code, c ∈ List.finRange 256 := by decide
  exact all _

theorem allMaps_nodup : allMaps.Nodup := by
  apply List.pairwise_map.mpr
  have hn : (List.finRange 256).Nodup := by decide
  exact hn.imp (fun hne heq => hne (mapOf_injective _ _ heq))

theorem actual_hom_count : homCount M8 K2 allMaps = 0 := by
  have he : (allMaps.filter fun f => decide (Hom M8 K2 f)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro f _ h
    exact no_hom_to_K2 f (of_decide_eq_true h)
  unfold homCount
  rw [he]
  rfl

theorem M8_not_Sidorenko : ¬ Sidorenko M8 := by
  intro h
  have hi := h 2 (by decide) K2 allMaps allMaps_nodup allMaps_complete
  rw [actual_edge_counts.1, actual_edge_counts.2, actual_hom_count] at hi
  have hn : ¬ ((2*1)^12 * 2^8 ≤ 0 * 2^(2*12)) := by decide
  exact hn hi

def AllMobiusLaddersSidorenko : Prop :=
  ∀ r : Nat, 2 ≤ r → ∀ H : Graph (2*r),
    (∀ i j, H.adj i j = mobiusAdj r i j) → Sidorenko H

theorem conjecture_4396_false : ¬ AllMobiusLaddersSidorenko := by
  intro h
  exact M8_not_Sidorenko (h 4 (by decide) M8 (fun _ _ => rfl))

#print axioms every_map_encoded
#print axioms allMaps_nodup
#print axioms M8_not_Sidorenko
#print axioms conjecture_4396_false
end Conjecture4396
