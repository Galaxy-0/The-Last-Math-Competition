import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Prod

namespace Conjecture1277

/-- A finite history with `n + 1` states, stored by successive appending. -/
def Word (α : Type*) : ℕ → Type _
  | 0 => α
  | n + 1 => Word α n × α

instance instFintypeWord {α : Type*} [Fintype α] (n : ℕ) : Fintype (Word α n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype α)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Word α n × α))

/-- The terminal state of a nonempty history. -/
def lastState {α : Type*} : {n : ℕ} → Word α n → α
  | 0, x => x
  | _ + 1, x => x.2

/-- The stored histories are exactly ordinary time-indexed state tuples. -/
def wordEquiv (α : Type*) : (n : ℕ) → Word α n ≃ (Fin (n + 1) → α)
  | 0 => (Equiv.funUnique (Fin 1) α).symm
  | n + 1 =>
    ((Equiv.prodCongr (wordEquiv α n) (Equiv.refl α)).trans
      (Equiv.prodComm _ _)).trans (Fin.snocEquiv (fun _ : Fin (n + 1 + 1) => α))

theorem wordEquiv_zero {α : Type*} (x : α) (i : Fin 1) : wordEquiv α 0 x i = x := rfl

theorem wordEquiv_succ {α : Type*} (n : ℕ) (x : Word α n) (y : α) :
    wordEquiv α (n + 1) (x, y) = Fin.snoc (wordEquiv α n x) y := rfl

theorem wordEquiv_last {α : Type*} (n : ℕ) (x : Word α n) :
    wordEquiv α n x (Fin.last n) = lastState x := by
  cases n with
  | zero => rfl
  | succ n =>
    rcases x with ⟨x, y⟩
    change @Fin.snoc (n + 1) (fun _ => α) (wordEquiv α n x) y (Fin.last (n + 1)) = y
    exact Fin.snoc_last _ _

end Conjecture1277
