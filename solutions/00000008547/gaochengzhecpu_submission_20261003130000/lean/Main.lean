import Std

/-! The five-element diamond M3 is geometric and Peck, and also strictly
Sperner. Its characteristic polynomial is t^2 - 3t + 2, not palindromic. -/
namespace Conjecture8547
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

abbrev E := Fin 5
abbrev Subset := Fin 32

structure LatticeData where
  le : E → E → Bool
  bot : E
  top : E
  meet : E → E → E
  join : E → E → E
  rank : E → Nat

def Below (L : LatticeData) (x y : E) : Prop := L.le x y = true
instance (L : LatticeData) (x y : E) : Decidable (Below L x y) :=
  inferInstanceAs (Decidable (L.le x y = true))

def LatticeLaws (L : LatticeData) : Prop :=
  (∀ x, Below L x x) ∧
  (∀ x y, Below L x y → Below L y x → x = y) ∧
  (∀ x y z, Below L x y → Below L y z → Below L x z) ∧
  (∀ x, Below L L.bot x ∧ Below L x L.top) ∧
  (∀ x y, Below L (L.meet x y) x ∧ Below L (L.meet x y) y) ∧
  (∀ x y z, Below L z x → Below L z y → Below L z (L.meet x y)) ∧
  (∀ x y, Below L x (L.join x y) ∧ Below L y (L.join x y)) ∧
  (∀ x y z, Below L x z → Below L y z → Below L (L.join x y) z)

def Covers (L : LatticeData) (x y : E) : Prop :=
  Below L x y ∧ x ≠ y ∧
  ∀ z, Below L x z → Below L z y → z = x ∨ z = y
instance (L : LatticeData) (x y : E) : Decidable (Covers L x y) := by
  unfold Covers; infer_instance

def Graded (L : LatticeData) : Prop :=
  L.rank L.bot = 0 ∧ ∀ x y, Covers L x y → L.rank y = L.rank x + 1

def atomsBelow (L : LatticeData) (x : E) : List E :=
  (List.finRange 5).filter fun a => decide (Covers L L.bot a ∧ Below L a x)
def Atomistic (L : LatticeData) : Prop :=
  ∀ x, (atomsBelow L x).foldl L.join L.bot = x
def Semimodular (L : LatticeData) : Prop :=
  ∀ x y, Covers L (L.meet x y) x → Covers L y (L.join x y)
def Geometric (L : LatticeData) : Prop :=
  LatticeLaws L ∧ Graded L ∧ Atomistic L ∧ Semimodular L

def diamond : LatticeData where
  le x y := decide (x = 0 ∨ y = 4 ∨ x = y)
  bot := 0
  top := 4
  meet x y := if x = 4 then y else if y = 4 then x else if x = y then x else 0
  join x y := if x = 0 then y else if y = 0 then x else if x = y then x else 4
  rank x := if x = 0 then 0 else if x = 4 then 2 else 1

theorem diamond_geometric : Geometric diamond := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold LatticeLaws; decide
  · unfold Graded; decide
  · unfold Atomistic; decide
  · unfold Semimodular; decide

def member (s : Subset) (x : E) : Bool := (s.val / 2^x.val) % 2 == 1
def cardinality (s : Subset) : Nat := ((List.finRange 5).filter (member s)).length
def encodeBits (b0 b1 b2 b3 b4 : Bool) : Subset :=
  ⟨((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
    (if b3 then 8 else 0) + (if b4 then 16 else 0)) % 32, Nat.mod_lt _ (by decide)⟩
def table (b0 b1 b2 b3 b4 : Bool) (x : E) : Bool :=
  match x.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | _ => b4
theorem encodeBits_correct : ∀ b0 b1 b2 b3 b4 : Bool, ∀ x : E,
    member (encodeBits b0 b1 b2 b3 b4) x = table b0 b1 b2 b3 b4 x := by decide
def encode (p : E → Bool) : Subset := encodeBits (p 0) (p 1) (p 2) (p 3) (p 4)
theorem every_subset_encoded (p : E → Bool) : member (encode p) = p := by
  funext x
  unfold encode
  rw [encodeBits_correct]
  have all : ∀ x : E, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
  rcases all x with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- This also covers arbitrary proposition-valued subsets, not only Boolean inputs. -/
theorem every_prop_subset_encoded (p : E → Prop) :
    ∃ s : Subset, ∀ x, member s x = true ↔ p x := by
  classical
  refine ⟨encode (fun x => decide (p x)), ?_⟩
  intro x
  rw [every_subset_encoded]
  simp

def Included (a b : Subset) : Prop := ∀ x, member a x = true → member b x = true
def Chain (L : LatticeData) (a : Subset) : Prop :=
  ∀ x y, member a x = true → member a y = true → Below L x y ∨ Below L y x
def Antichain (L : LatticeData) (a : Subset) : Prop :=
  ∀ x y, member a x = true → member a y = true → Below L x y → x = y
instance (a b : Subset) : Decidable (Included a b) := by unfold Included; infer_instance
instance (L : LatticeData) (a : Subset) : Decidable (Chain L a) := by unfold Chain; infer_instance
instance (L : LatticeData) (a : Subset) : Decidable (Antichain L a) := by unfold Antichain; infer_instance

/-- A k-family has no chain containing more than k elements. -/
def KFamily (L : LatticeData) (k : Nat) (a : Subset) : Prop :=
  ∀ c : Subset, Included c a → Chain L c → cardinality c ≤ k
instance (L : LatticeData) (k : Nat) (a : Subset) : Decidable (KFamily L k a) := by
  unfold KFamily; infer_instance

def layer (L : LatticeData) (r : Nat) : Subset := encode (fun x => decide (L.rank x = r))
def rankSizes (L : LatticeData) : List Nat :=
  (List.range (L.rank L.top + 1)).map (fun r => cardinality (layer L r))
def insertDescending (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: rest => if b ≤ a then a :: b :: rest else b :: insertDescending a rest
def sortDescending : List Nat → List Nat
  | [] => []
  | a :: rest => insertDescending a (sortDescending rest)
def largestRankSum (L : LatticeData) (k : Nat) : Nat :=
  ((sortDescending (rankSizes L)).take k).sum
def RankSymmetric (L : LatticeData) : Prop :=
  ∀ i : Fin (L.rank L.top + 1),
    cardinality (layer L i.val) = cardinality (layer L (L.rank L.top - i.val))
def UnimodalAt (L : LatticeData) (peak : Nat) : Prop :=
  peak ≤ L.rank L.top ∧ ∀ i : Fin (L.rank L.top),
    (i.val < peak → cardinality (layer L i.val) ≤ cardinality (layer L (i.val+1))) ∧
    (peak ≤ i.val → cardinality (layer L (i.val+1)) ≤ cardinality (layer L i.val))
def StrongSperner (L : LatticeData) : Prop :=
  ∀ k : Nat,
    (∀ a : Subset, KFamily L k a → cardinality a ≤ largestRankSum L k) ∧
    ∃ a : Subset, KFamily L k a ∧ cardinality a = largestRankSum L k
def Peck (L : LatticeData) : Prop :=
  RankSymmetric L ∧ (∃ peak, UnimodalAt L peak) ∧ StrongSperner L
def StrictSperner (L : LatticeData) : Prop :=
  ∀ a : Subset, Antichain L a → cardinality a = largestRankSum L 1 →
    ∃ i : Fin (L.rank L.top+1), a = layer L i.val

theorem diamond_rank_sizes : rankSizes diamond = [1,3,1] := by decide
theorem diamond_rank_symmetric : RankSymmetric diamond := by unfold RankSymmetric; decide
theorem diamond_unimodal : UnimodalAt diamond 1 := by unfold UnimodalAt; decide
theorem largestRankSum_explicit (k : Nat) :
    largestRankSum diamond k = ([3,1,1].take k).sum := by rfl
theorem all_chains_small : ∀ c : Subset, Chain diamond c → cardinality c ≤ 3 := by decide
theorem all_subsets_small : ∀ a : Subset, cardinality a ≤ 5 := by decide

theorem diamond_strong_sperner : StrongSperner diamond := by
  intro k
  cases k with
  | zero =>
    constructor
    · decide
    · exact ⟨0, by decide, by decide⟩
  | succ k =>
    cases k with
    | zero =>
      constructor
      · decide
      · exact ⟨14, by decide, by decide⟩
    | succ k =>
      cases k with
      | zero =>
        constructor
        · decide
        · exact ⟨15, by decide, by decide⟩
      | succ k =>
        have hsum : largestRankSum diamond (k+1+1+1) = 5 := by
          rw [largestRankSum_explicit]
          simp
        constructor
        · intro a _
          rw [hsum]
          exact all_subsets_small a
        · refine ⟨31, ?_, ?_⟩
          · intro c _ hc
            have ht := all_chains_small c hc
            omega
          · rw [hsum]; decide

theorem diamond_peck : Peck diamond :=
  ⟨diamond_rank_symmetric, ⟨1, diamond_unimodal⟩, diamond_strong_sperner⟩

theorem unique_maximum_antichain : ∀ a : Subset,
    Antichain diamond a → cardinality a = 3 → a = 14 := by decide
theorem diamond_strict_sperner : StrictSperner diamond := by
  intro a ha hs
  have heq : cardinality a = 3 := hs
  have h := unique_maximum_antichain a ha heq
  refine ⟨⟨1, by decide⟩, ?_⟩
  rw [h]
  decide

/- The usual bottom-interval Moebius function is characterized by the
   convolution recurrence sum_{y <= x} mu(y) = [x = bottom]. -/
def MobiusRecurrence (L : LatticeData) (mu : E → Int) : Prop :=
  ∀ x, (((List.finRange 5).filter (fun y => L.le y x)).map mu).sum =
    if x = L.bot then 1 else 0

def diamondMobius (x : E) : Int := if x = 0 then 1 else if x = 4 then 2 else -1

theorem diamond_mobius_recurrence : MobiusRecurrence diamond diamondMobius := by
  unfold MobiusRecurrence
  decide

theorem diamond_mobius_unique (mu : E → Int) (h : MobiusRecurrence diamond mu) :
    mu = diamondMobius := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  change mu 0 + 0 = 1 at h0
  change mu 0 + (mu 1 + 0) = 0 at h1
  change mu 0 + (mu 2 + 0) = 0 at h2
  change mu 0 + (mu 3 + 0) = 0 at h3
  change mu 0 + (mu 1 + (mu 2 + (mu 3 + (mu 4 + 0)))) = 0 at h4
  funext x
  have all : ∀ x : E, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by decide
  rcases all x with rfl | rfl | rfl | rfl | rfl <;> simp [diamondMobius] <;> omega

/-- The coefficient of t^k in sum_x mu(0,x) t^(rank(top)-rank(x)). -/
def characteristicCoefficient (L : LatticeData) (mu : E → Int) (k : Nat) : Int :=
  (((List.finRange 5).filter (fun x => decide (L.rank L.top - L.rank x = k))).map mu).sum

def characteristicAt (L : LatticeData) (mu : E → Int) (t : Int) : Int :=
  ((List.finRange 5).map (fun x => mu x * t ^ (L.rank L.top - L.rank x))).sum

def CoefficientSymmetric (L : LatticeData) (mu : E → Int) : Prop :=
  ∀ i : Fin (L.rank L.top+1),
    characteristicCoefficient L mu i.val =
      characteristicCoefficient L mu (L.rank L.top-i.val)

theorem diamond_characteristic_coefficients :
    [characteristicCoefficient diamond diamondMobius 0,
     characteristicCoefficient diamond diamondMobius 1,
     characteristicCoefficient diamond diamondMobius 2] = [2,-3,1] := by decide

theorem diamond_not_coefficient_symmetric :
    ¬ CoefficientSymmetric diamond diamondMobius := by
  intro h
  have h0 := h ⟨0, by decide⟩
  have bad : (2 : Int) = 1 := h0
  omega

/-- Even reflection of the values, or of the roots, about rank/2 = 1 fails. -/
theorem diamond_root_reflection_fails :
    ¬ (∀ t : Int, characteristicAt diamond diamondMobius t = 0 →
       characteristicAt diamond diamondMobius (2-t) = 0) := by
  intro h
  have h2 := h 2 (by decide)
  have bad : (2 : Int) = 0 := h2
  omega

theorem diamond_value_reflection_fails :
    ¬ (∀ t : Int, characteristicAt diamond diamondMobius t =
       characteristicAt diamond diamondMobius (2-t)) := by
  intro h
  have h0 := h 0
  have bad : (2 : Int) = 0 := h0
  omega

/-- A necessary specialization of the conjecture's universal assertion to
    five-element lattices; the extra StrictSperner assumption strengthens
    the counterexample and accommodates the source's stated definition. -/
def GeometricPeckSymmetryAssertion : Prop :=
  ∀ L : LatticeData, ∀ mu : E → Int,
    Geometric L → Peck L → StrictSperner L → MobiusRecurrence L mu →
      CoefficientSymmetric L mu

theorem conjecture_8547_false : ¬ GeometricPeckSymmetryAssertion := by
  intro h
  exact diamond_not_coefficient_symmetric
    (h diamond diamondMobius diamond_geometric diamond_peck
      diamond_strict_sperner diamond_mobius_recurrence)

#print axioms every_prop_subset_encoded
#print axioms diamond_geometric
#print axioms diamond_peck
#print axioms diamond_strict_sperner
#print axioms diamond_mobius_unique
#print axioms diamond_root_reflection_fails
#print axioms conjecture_8547_false

end Conjecture8547
