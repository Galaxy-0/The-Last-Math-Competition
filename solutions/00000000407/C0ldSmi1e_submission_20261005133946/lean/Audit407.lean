import Conjecture407

namespace Conjecture407Audit

/-- A real LR tableau of empty shape and empty content. -/
noncomputable def emptyTableau : Conjecture407.LRTableau ⊥ ⊥ ⊥ where
  entry := fun _ => 0
  contained := le_rfl
  rowWeak := by intros; exact le_rfl
  colStrict := by
    intro a
    exact ((Finset.mem_sdiff.mp a.property).2 (Finset.mem_sdiff.mp a.property).1).elim
  content := by
    intro i
    rw [YoungDiagram.rowLen_eq_card]
    simp [Conjecture407.entryCount, YoungDiagram.row]
  lattice := by
    intro b
    exact ((Finset.mem_sdiff.mp b.property).2 (Finset.mem_sdiff.mp b.property).1).elim

/-- A nonzero standard LR coefficient, checking the definition is not identically zero. -/
theorem empty_coefficient_one : Conjecture407.lrCoefficient ⊥ ⊥ ⊥ = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨emptyTableau, ?_⟩
  intro T
  apply Conjecture407.LRTableau.entry_injective
  funext a
  exact ((Finset.mem_sdiff.mp a.property).2 (Finset.mem_sdiff.mp a.property).1).elim

/-- The only partition of zero is the empty Young diagram. -/
noncomputable def emptyPartition : Conjecture407.Partition 0 := ⟨⊥, rfl⟩

theorem partition_zero_unique (d : Conjecture407.Partition 0) : d = emptyPartition := by
  apply Subtype.ext
  apply YoungDiagram.ext
  exact Finset.card_eq_zero.mp d.property

/-- The exceptional n=0 table has its single nonzero entry. -/
theorem table_zero_one : Conjecture407.nonzeroCount 0 = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  let t : Conjecture407.NonzeroEntry 0 :=
    ⟨(emptyPartition, emptyPartition, emptyPartition), by
      change Conjecture407.lrCoefficient ⊥ ⊥ ⊥ ≠ 0
      rw [empty_coefficient_one]
      norm_num⟩
  refine ⟨t, ?_⟩
  intro u
  apply Subtype.ext
  change u.val = (emptyPartition, emptyPartition, emptyPartition)
  rcases u.val with ⟨a,b,c⟩
  simp only [partition_zero_unique]

/-- The literal n=1 and n=2 tables have no nonzero entries. -/
theorem table_one_zero : Conjecture407.nonzeroCount 1 = 0 :=
  Conjecture407.nonzeroCount_eq_zero 1 (by norm_num)

theorem table_two_zero : Conjecture407.nonzeroCount 2 = 0 :=
  Conjecture407.nonzeroCount_eq_zero 2 (by norm_num)

end Conjecture407Audit

#check Conjecture407.Partition
#check Conjecture407.SkewCell
#check Conjecture407.ReadingLE
#check Conjecture407.entryCount
#check Conjecture407.prefixCount
#check Conjecture407.LRTableau
#check Conjecture407.lrTableauFinite
#check Conjecture407.diagram_card_eq_sum_rowLen
#check Conjecture407.LRTableau.size_balance
#check Conjecture407.lrCoefficient
#check Conjecture407.partitionFinite
#check Conjecture407.NonzeroEntry
#check Conjecture407.nonzeroEntryFinite
#check Conjecture407.nonzeroCount
#check Conjecture407.scale
#check Conjecture407.RatioAsymptotic
#check Conjecture407.not_ratioAsymptotic
#check Conjecture407.no_real_ratio_constant
#check Conjecture407.conjecture407_false

#print axioms Conjecture407.LRTableau.entry_lt
#print axioms Conjecture407.lrTableauFinite
#print axioms Conjecture407.LRTableau.size_balance
#print axioms Conjecture407.partitionFinite
#print axioms Conjecture407.nonzeroEntryFinite
#print axioms Conjecture407.lrCoefficient_eq_zero
#print axioms Conjecture407.nonzeroCount_eq_zero
#print axioms Conjecture407.normalized_tendsto_zero
#print axioms Conjecture407.not_ratioAsymptotic
#print axioms Conjecture407.no_real_ratio_constant
#print axioms Conjecture407.conjecture407_false
#print axioms Conjecture407Audit.empty_coefficient_one
#print axioms Conjecture407Audit.table_zero_one
#print axioms Conjecture407Audit.table_one_zero
#print axioms Conjecture407Audit.table_two_zero

#print Conjecture407.LRTableau
