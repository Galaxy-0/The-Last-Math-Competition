import Std

/-!
Conjecture 1665: the claimed tight family is false.
The counterexample is the Cartesian product of the standard Petersen graph
and the two-vertex path.  The graph, legal ignition process, completion,
and contradiction to the claimed minimum are all checked below.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Conjecture1665

def petersen (u v : Nat) : Prop :=
  (u < 5 ∧ v < 5 ∧ ((u + 1) % 5 = v ∨ (v + 1) % 5 = u)) ∨
  (5 ≤ u ∧ 5 ≤ v ∧ (((u - 5) + 2) % 5 = v - 5 ∨
    ((v - 5) + 2) % 5 = u - 5)) ∨
  (u % 5 = v % 5 ∧ ((u < 5 ∧ 5 ≤ v) ∨ (v < 5 ∧ 5 ≤ u)))

instance (u v : Nat) : Decidable (petersen u v) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def petPath (m : Nat) (u v : Fin (10 * m)) : Prop :=
  (u.val / 10 = v.val / 10 ∧ petersen (u.val % 10) (v.val % 10)) ∨
  (u.val % 10 = v.val % 10 ∧
    (u.val / 10 + 1 = v.val / 10 ∨ v.val / 10 + 1 = u.val / 10))

instance (m : Nat) (u v : Fin (10 * m)) : Decidable (petPath m u v) :=
  inferInstanceAs (Decidable (_ ∨ _))

def encode (u : Fin 10) (j : Fin 2) : Fin 20 :=
  ⟨u.val + 10 * j.val, by omega⟩

theorem product_encoding : ∀ u v : Fin 10, ∀ i j : Fin 2,
    petPath 2 (encode u i) (encode v j) ↔
    (i = j ∧ petersen u.val v.val) ∨
      (u = v ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) := by decide

theorem product_encoding_bijective :
    (∀ x : Fin 20, ∃ u : Fin 10, ∃ j : Fin 2, encode u j = x) ∧
    (∀ u v : Fin 10, ∀ i j : Fin 2, encode u i = encode v j → u = v ∧ i = j) := by
  constructor
  · intro x
    refine ⟨⟨x.val % 10, Nat.mod_lt _ (by decide)⟩, ⟨x.val / 10, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [encode]
    omega
  · intro u v i j h
    have hh := congrArg Fin.val h
    simp only [encode] at hh
    constructor <;> apply Fin.ext <;> omega

theorem graph_simple :
    (∀ u : Fin 20, ¬petPath 2 u u) ∧
    (∀ u v : Fin 20, petPath 2 u v ↔ petPath 2 v u) := by decide

def advance {n : Nat} (adj : Fin n → Fin n → Prop)
    [DecidableRel adj] (burned : Fin n → Bool) (source : Fin n) : Fin n → Bool :=
  fun v => decide (v = source) || burned v ||
    (List.finRange n).any (fun u => burned u && decide (adj u v))

def run {n : Nat} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (burned : Fin n → Bool) : List (Fin n) → Fin n → Bool
  | [] => burned
  | x :: xs => run adj (advance adj burned x) xs

/- Sources must be unburned at the beginning of their round. During a
round, older fires spread one edge and the new source catches fire. -/
def legal {n : Nat} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (burned : Fin n → Bool) : List (Fin n) → Bool
  | [] => true
  | x :: xs => !burned x && legal adj (advance adj burned x) xs

def BurnsIn {n : Nat} (adj : Fin n → Fin n → Prop) [DecidableRel adj] (k : Nat) : Prop :=
  ∃ sources : List (Fin n), sources.length ≤ k ∧
    legal adj (fun _ => false) sources = true ∧
    ∀ v, run adj (fun _ => false) sources v = true

def BurningNumberIs {n : Nat} (adj : Fin n → Fin n → Prop)
    [DecidableRel adj] (b : Nat) : Prop :=
  BurnsIn adj b ∧ ∀ k, k < b → ¬BurnsIn adj k

def sources : List (Fin 20) := [0, 1, 2, 12]

theorem legal_sources : legal (petPath 2) (fun _ => false) sources = true := by decide

theorem all_burned : ∀ v : Fin 20,
    run (petPath 2) (fun _ => false) sources v = true := by decide

theorem burns_in_four : BurnsIn (petPath 2) 4 := by
  exact ⟨sources, by decide, legal_sources, all_burned⟩

/- For n > 0 this is the integer characterization of r = ceil(sqrt(n)). -/
def CeilSqrtIs (n r : Nat) : Prop := (r - 1)^2 < n ∧ n ≤ r^2

theorem ceil_sqrt_twenty : CeilSqrtIs 20 5 := by unfold CeilSqrtIs; decide

/- This is the universally quantified tight-family clause of the original
conjecture, with the m-vertex path, m > 0. -/
def TightFamilyClaim : Prop := ∀ m r : Nat, 0 < m →
  CeilSqrtIs (10 * m) r → BurningNumberIs (petPath m) (r + 1)

theorem not_tight_family_claim : ¬TightFamilyClaim := by
  intro h
  have claimed := h 2 5 (by decide) ceil_sqrt_twenty
  exact claimed.2 4 (by decide) burns_in_four

#print axioms not_tight_family_claim
#print axioms product_encoding
#print axioms all_burned
end Conjecture1665
