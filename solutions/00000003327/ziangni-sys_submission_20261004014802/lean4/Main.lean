import Std

/-!
# Conjecture 00000003327: Fine numbers are not log-concave

`true` encodes U = (1,1), `false` encodes D = (1,-1).
Fine numbers count Dyck paths with no hill (a peak at height one).
The definitions enumerate words, rather than assuming any Fine-number values.
-/

namespace FineCounterexample

abbrev Word := List Bool

/-- All step words of length m, each once. -/
def words : Nat → List Word
  | 0 => [[]]
  | m + 1 => (words m).map (true :: ·) ++ (words m).map (false :: ·)

theorem mem_words (m : Nat) (w : Word) : w ∈ words m ↔ w.length = m := by
  induction m generalizing w with
  | zero => simp [words]
  | succ m ih =>
    cases w with
    | nil => simp [words]
    | cons b w => cases b <;> simp [words, ih]

theorem words_nodup (m : Nat) : (words m).Nodup := by
  induction m with
  | zero => simp [words]
  | succ m ih =>
    simp only [words, List.Nodup, List.pairwise_append, List.pairwise_map,
      List.cons.injEq, true_and, ne_eq, List.forall_mem_map]
    exact ⟨ih, ih, by simp⟩

/-- Scan a path from height h; reject a down-step from zero, a hill,
or a final height other than zero. -/
def hillFreeFrom : Nat → Word → Bool
  | h, [] => h == 0
  | h, true :: w =>
      if h == 0 && w.head? == some false then false
      else hillFreeFrom (h + 1) w
  | 0, false :: _ => false
  | h + 1, false :: w => hillFreeFrom h w

/-- Declarative recursive condition for staying nonnegative and ending at zero. -/
def DyckFrom : Nat → Word → Prop
  | h, [] => h = 0
  | h, true :: w => DyckFrom (h + 1) w
  | 0, false :: _ => False
  | h + 1, false :: w => DyckFrom h w

/-- No up-step starting at height zero is immediately followed by a down-step. -/
def NoHillsFrom : Nat → Word → Prop
  | _, [] => True
  | h, true :: w => (h = 0 → w.head? ≠ some false) ∧ NoHillsFrom (h + 1) w
  | h, false :: w => NoHillsFrom (h - 1) w

theorem hillFreeFrom_iff (w : Word) (h : Nat) :
    hillFreeFrom h w = true ↔ DyckFrom h w ∧ NoHillsFrom h w := by
  induction w generalizing h with
  | nil => simp [hillFreeFrom, DyckFrom, NoHillsFrom]
  | cons b w ih =>
    cases b with
    | false => cases h <;> simp [hillFreeFrom, DyckFrom, NoHillsFrom, ih]
    | true =>
      by_cases hh : h = 0 <;>
        simp [hillFreeFrom, DyckFrom, NoHillsFrom, ih, hh, and_left_comm]

/-- Hill-free Dyck paths of semilength n. -/
def paths (n : Nat) : List Word := (words (2 * n)).filter (hillFreeFrom 0)

theorem mem_paths (n : Nat) (w : Word) :
    w ∈ paths n ↔ w.length = 2 * n ∧ hillFreeFrom 0 w = true := by
  simp [paths, mem_words]

theorem paths_nodup (n : Nat) : (paths n).Nodup :=
  (words_nodup (2 * n)).filter (hillFreeFrom 0)

theorem mem_paths_iff (n : Nat) (w : Word) :
    w ∈ paths n ↔ w.length = 2 * n ∧ DyckFrom 0 w ∧ NoHillsFrom 0 w := by
  rw [mem_paths, hillFreeFrom_iff]

def fine (n : Nat) : Nat := (paths n).length

theorem fine_two : fine 2 = 1 := by decide
theorem fine_three : fine 3 = 2 := by decide
theorem fine_four : fine 4 = 6 := by decide

/-- The positive tail is used so that the zero F_1 is irrelevant. -/
def LogConcavePositiveTail (a : Nat → Nat) : Prop :=
  ∀ n : Nat, 3 ≤ n → a (n - 1) * a (n + 1) ≤ a n * a n

theorem violation : fine 3 * fine 3 < fine 2 * fine 4 := by decide

theorem not_logConcavePositiveTail : ¬ LogConcavePositiveTail fine := by
  intro h
  have bad := h 3 (by decide)
  change fine 2 * fine 4 ≤ fine 3 * fine 3 at bad
  exact (Nat.not_le_of_gt violation) bad

/-- The standard full log-concavity clause stated in the conjecture. -/
def LogConcave (a : Nat → Nat) : Prop :=
  ∀ n : Nat, 1 ≤ n → a (n - 1) * a (n + 1) ≤ a n * a n

theorem conjecture_00000003327_false : ¬ LogConcave fine := by
  intro h
  have bad := h 3 (by decide)
  change fine 2 * fine 4 ≤ fine 3 * fine 3 at bad
  exact (Nat.not_le_of_gt violation) bad

end FineCounterexample

#print axioms FineCounterexample.fine_two
#print axioms FineCounterexample.mem_paths_iff
#print axioms FineCounterexample.paths_nodup
#print axioms FineCounterexample.fine_three
#print axioms FineCounterexample.fine_four
#print axioms FineCounterexample.violation
#print axioms FineCounterexample.not_logConcavePositiveTail
#print axioms FineCounterexample.conjecture_00000003327_false
