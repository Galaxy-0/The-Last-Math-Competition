import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ext

namespace Shor
abbrev F₂ := ZMod 2
abbrev V := Fin 5 → F₂
abbrev A := Fin 4 → F₂
def E (i : Fin 4) (j : Fin 5) : F₂ := if j.val=i.val ∨ j.val=i.val+1 then 1 else 0
def parity (v : V) : F₂ := ∑ j,v j
def synthE (a : A) : V := fun j => ∑ i,a i * E i j
def adjDot (i : Fin 4) (v : V) : F₂ := ∑ j,E i j * v j
def weight (v : V) : ℕ := (Finset.univ.filter (fun j => v j≠0)).card

set_option maxRecDepth 200000 in
set_option maxHeartbeats 3000000 in
theorem parity_span : ∀ v : V, parity v=0 ↔ ∃ a : A,synthE a=v := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 3000000 in
theorem adjacent_constant : ∀ v : V, (∀ i : Fin 4,adjDot i v=0) ↔ ∃ t : F₂,∀ j,v j=t := by decide

theorem parity_constant : ∀ t : F₂,parity (fun _ : Fin 5 => t)=t := by decide
theorem parity_basis : ∀ b : Fin 5,parity (fun c : Fin 5 => if c=b then 1 else 0)=1 := by decide
theorem even_pair : ∀ i : Fin 4,parity (E i)=0 := by decide
theorem constant_weight : ∀ t : F₂,t≠0 → weight (fun _ : Fin 5 => t)=5 := by decide
theorem nonzero_of_parity {v : V} (hv : parity v≠0) : ∃ j,v j≠0 := by
  by_contra h
  have hz : ∀ j,v j=0 := by simpa using h
  exact hv (by simp [parity,hz])
end Shor
