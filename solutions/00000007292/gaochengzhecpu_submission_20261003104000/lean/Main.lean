import Std

/-! Conjecture 7292: Dyson rank and the Andrews--Garvan crank are not
equidistributed on the integer partitions of four.  The exhaustive list is
proved complete for arbitrary positive, weakly decreasing lists of sum four. -/

namespace Conjecture7292

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- A partition is its list of positive parts in weakly decreasing order. -/
def IsPartition (n : Nat) (parts : List Nat) : Prop :=
  parts.Pairwise (fun a b => b ≤ a) ∧
  (∀ a ∈ parts, 0 < a) ∧ parts.sum = n

instance (n : Nat) (parts : List Nat) : Decidable (IsPartition n parts) :=
  inferInstanceAs (Decidable (parts.Pairwise (fun a b => b ≤ a) ∧
    (∀ a ∈ parts, 0 < a) ∧ parts.sum = n))

/-- Dyson's rank, with subtraction performed in the integers. -/
def rank (parts : List Nat) : Int :=
  Int.ofNat (parts.headD 0) - Int.ofNat parts.length

def ones (parts : List Nat) : Nat :=
  (parts.filter (fun a => a == 1)).length

/-- The Andrews--Garvan crank of an ordinary partition. -/
def crank (parts : List Nat) : Int :=
  if ones parts = 0 then Int.ofNat (parts.headD 0)
  else Int.ofNat ((parts.filter (fun a => decide (ones parts < a))).length)
    - Int.ofNat (ones parts)

def partitionsFour : List (List Nat) :=
  [[4], [3,1], [2,2], [2,1,1], [1,1,1,1]]

theorem length_le_sum_of_positive (parts : List Nat)
    (h : ∀ a ∈ parts, 0 < a) : parts.length ≤ parts.sum := by
  induction parts with
  | nil => simp
  | cons a parts ih =>
    have ha : 0 < a := h a (by simp)
    have hp : ∀ b ∈ parts, 0 < b := by
      intro b hb
      exact h b (by simp [hb])
    have hi := ih hp
    simp only [List.length_cons, List.sum_cons]
    omega

/-- A symbolic completeness proof: there are no unlisted partitions. -/
theorem partitionsFour_complete (parts : List Nat)
    (h : IsPartition 4 parts) : parts ∈ partitionsFour := by
  have hl : parts.length ≤ 4 := by
    have ht := length_le_sum_of_positive parts h.2.1
    rw [h.2.2] at ht
    exact ht
  rcases h with ⟨ho, hp, hs⟩
  cases parts with
  | nil => simp at hs
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hs
      subst a
      decide
    | cons b rest =>
      cases rest with
      | nil =>
        simp [List.pairwise_cons] at ho
        simp at hp
        simp at hs
        simp [partitionsFour]
        omega
      | cons c rest =>
        cases rest with
        | nil =>
          simp [List.pairwise_cons] at ho
          simp at hp
          simp at hs
          simp [partitionsFour]
          omega
        | cons d rest =>
          cases rest with
          | nil =>
            simp [List.pairwise_cons] at ho
            simp at hp
            simp at hs
            simp [partitionsFour]
            omega
          | cons e tail =>
            simp only [List.length_cons] at hl
            omega

theorem partitionsFour_sound :
    ∀ parts ∈ partitionsFour, IsPartition 4 parts := by decide

theorem partitionsFour_exact (parts : List Nat) :
    parts ∈ partitionsFour ↔ IsPartition 4 parts :=
  ⟨partitionsFour_sound parts, partitionsFour_complete parts⟩

theorem partitionsFour_nodup : partitionsFour.Nodup := by decide

/-- Every listed part is at most the first, so headD is the largest part. -/
theorem first_is_largest (n : Nat) (a : Nat) (tail : List Nat)
    (h : IsPartition n (a :: tail)) : ∀ b ∈ a :: tail, b ≤ a := by
  have hfirst : ∀ b ∈ tail, b ≤ a := (List.pairwise_cons.mp h.1).1
  intro b hb
  rcases List.mem_cons.mp hb with heq | hb
  · subst b
    exact Nat.le_refl a
  · exact hfirst b hb

def frequency (stat : List Nat → Int) (value : Int) : Nat :=
  (partitionsFour.filter (fun parts => decide (stat parts = value))).length

theorem rank_values : partitionsFour.map rank = [3,1,0,-1,-3] := by decide
theorem crank_values : partitionsFour.map crank = [4,0,2,-2,-4] := by decide

theorem rank_four_frequency : frequency rank 4 = 0 := by decide
theorem crank_four_frequency : frequency crank 4 = 1 := by decide

def EquidistributedOnFour : Prop :=
  ∀ value : Int, frequency rank value = frequency crank value

theorem not_equidistributed_on_four : ¬EquidistributedOnFour := by
  intro h
  have bad := h 4
  rw [rank_four_frequency, crank_four_frequency] at bad
  omega

/-- Counting over any complete duplicate-free list is ordinary cardinality.
The universal claim thus has no restriction to our chosen enumeration. -/
def RankCrankEquidistribution : Prop :=
  ∀ (n : Nat) (allParts : List (List Nat)), allParts.Nodup →
    (∀ parts, parts ∈ allParts ↔ IsPartition n parts) →
    ∀ value : Int,
      (allParts.filter (fun parts => decide (rank parts = value))).length =
      (allParts.filter (fun parts => decide (crank parts = value))).length

/-- Negates the original equidistribution clause using completeness and
absence of duplicates, as well as the unequal actual fiber cardinalities. -/
theorem conjecture7292_counterexample : ¬RankCrankEquidistribution := by
  intro h
  apply not_equidistributed_on_four
  exact h 4 partitionsFour partitionsFour_nodup partitionsFour_exact

/-- A count-free formulation over all partitions, independent of list choice. -/
theorem no_partition_four_has_rank_four :
    ∀ parts, IsPartition 4 parts → rank parts ≠ 4 := by
  intro parts hp
  have hm := partitionsFour_complete parts hp
  have checked : ∀ ps ∈ partitionsFour, rank ps ≠ 4 := by decide
  exact checked parts hm

theorem exists_partition_four_with_crank_four :
    ∃ parts, IsPartition 4 parts ∧ crank parts = 4 := by
  exact ⟨[4], by decide, by decide⟩

/-- Thus even equality of the two supports, weaker than equidistribution,
fails on the full standard set of partitions. -/
theorem not_equal_supports : ¬ (∀ value : Int,
    (∃ parts, IsPartition 4 parts ∧ rank parts = value) ↔
    (∃ parts, IsPartition 4 parts ∧ crank parts = value)) := by
  intro h
  rcases (h 4).mpr exists_partition_four_with_crank_four with ⟨parts, hp, hr⟩
  exact no_partition_four_has_rank_four parts hp hr

#print axioms partitionsFour_complete
#print axioms partitionsFour_exact
#print axioms partitionsFour_nodup
#print axioms first_is_largest
#print axioms conjecture7292_counterexample
#print axioms not_equal_supports

end Conjecture7292
