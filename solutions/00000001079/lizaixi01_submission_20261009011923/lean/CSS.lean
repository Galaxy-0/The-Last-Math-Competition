import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ext
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi

namespace BinaryCSS
abbrev F₂ := ZMod 2
abbrev Word (Q : Type*) := Q → F₂
abbrev Pauli (Q : Type*) := Word Q × Word Q

def dot {Q : Type*} [Fintype Q] (x y : Word Q) : F₂ := ∑ q, x q * y q
def synth {Q R : Type*} [Fintype R] (H : R → Word Q) (a : R → F₂) : Word Q :=
  fun q => ∑ r, a r * H r q
def rowspace {Q R : Type*} [Fintype R] (H : R → Word Q) (x : Word Q) : Prop :=
  ∃ a : R → F₂, synth H a = x

structure Code (Q RX RZ : Type*) [Fintype Q] where
  X : RX → Word Q
  Z : RZ → Word Q
  orthogonal : ∀ r s, dot (X r) (Z s) = 0

variable {Q RX RZ : Type*} [Fintype Q] [Fintype RX] [Fintype RZ]

theorem rowspace_zero (H : RX → Word Q) : rowspace H 0 := by
  refine ⟨0, ?_⟩
  ext q
  simp [synth]

theorem rowspace_row (H : RX → Word Q) (r : RX) : rowspace H (H r) := by
  classical
  refine ⟨(fun i => if i=r then 1 else 0), ?_⟩
  ext q
  simp [synth]

theorem rowspace_add (H : RX → Word Q) {x y : Word Q}
    (hx : rowspace H x) (hy : rowspace H y) : rowspace H (x+y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  refine ⟨a+b, ?_⟩
  ext q
  simp [synth,add_mul,Finset.sum_add_distrib]

theorem rowspace_smul (H : RX → Word Q) (c : F₂) {x : Word Q}
    (hx : rowspace H x) : rowspace H (c • x) := by
  obtain ⟨a,rfl⟩ := hx
  refine ⟨c • a, ?_⟩
  ext q
  simp [synth,Finset.mul_sum,mul_assoc]

def stabilizer (C : Code Q RX RZ) : Submodule F₂ (Pauli Q) where
  carrier := {p | rowspace C.X p.1 ∧ rowspace C.Z p.2}
  zero_mem' := ⟨rowspace_zero _,rowspace_zero _⟩
  add_mem' := fun hp hq => ⟨rowspace_add _ hp.1 hq.1,rowspace_add _ hp.2 hq.2⟩
  smul_mem' := fun c p hp => ⟨rowspace_smul _ c hp.1,rowspace_smul _ c hp.2⟩

def generator (C : Code Q RX RZ) : RX ⊕ RZ → Pauli Q
  | .inl r => (C.X r,0)
  | .inr s => (0,C.Z s)

theorem pauli_sum_fst (s : Finset RX) (f : RX → Pauli Q) :
    (∑ r ∈ s, f r).1 = ∑ r ∈ s, (f r).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih => simp [Finset.sum_insert hr,ih]

theorem pauli_sum_snd (s : Finset RX) (f : RX → Pauli Q) :
    (∑ r ∈ s, f r).2 = ∑ r ∈ s, (f r).2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih => simp [Finset.sum_insert hr,ih]

theorem stabilizer_eq_span (C : Code Q RX RZ) :
    stabilizer C = Submodule.span F₂ (Set.range (generator C)) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := hp
    have hx : (synth C.X a, (0 : Word Q)) ∈ Submodule.span F₂ (Set.range (generator C)) := by
      have he : (synth C.X a, (0 : Word Q)) = ∑ r : RX, a r • generator C (.inl r) := by
        ext q <;> simp [synth,generator,pauli_sum_fst,pauli_sum_snd,Finset.sum_apply]
      rw [he]
      apply Submodule.sum_mem
      intro r _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inl r,rfl⟩)
    have hz : ((0 : Word Q), synth C.Z b) ∈ Submodule.span F₂ (Set.range (generator C)) := by
      have he : ((0 : Word Q), synth C.Z b) = ∑ r : RZ, b r • generator C (.inr r) := by
        ext q <;> simp [synth,generator,pauli_sum_fst,pauli_sum_snd,Finset.sum_apply]
      rw [he]
      apply Submodule.sum_mem
      intro r _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr r,rfl⟩)
    have h := Submodule.add_mem _ hx hz
    simpa [ha,hb] using h
  · apply Submodule.span_le.mpr
    rintro p ⟨r,rfl⟩
    cases r with
    | inl r => exact ⟨rowspace_row _ r,rowspace_zero _⟩
    | inr s => exact ⟨rowspace_zero _,rowspace_row _ s⟩

def symp (p q : Pauli Q) : F₂ := dot p.1 q.2 + dot p.2 q.1
def centralizer (C : Code Q RX RZ) (p : Pauli Q) : Prop :=
  ∀ s : Pauli Q, s ∈ stabilizer C → symp s p = 0
def logical (C : Code Q RX RZ) (p : Pauli Q) : Prop := centralizer C p ∧ p ∉ stabilizer C
noncomputable def sweight (p : Pauli Q) : ℕ := by
  classical
  exact (Finset.univ.filter (fun q => p.1 q ≠ 0 ∨ p.2 q ≠ 0)).card
def HasQuantumDistance (C : Code Q RX RZ) (d : ℕ) : Prop :=
  (∃ p, logical C p ∧ sweight p=d) ∧ ∀ p, logical C p → d ≤ sweight p

theorem dot_synth (H : RX → Word Q) (a : RX → F₂) (x : Word Q) :
    dot (synth H a) x = ∑ r, a r * dot (H r) x := by
  simp only [dot,synth,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

theorem dot_comm (x y : Word Q) : dot x y = dot y x := by simp [dot,mul_comm]

theorem centralizer_iff (C : Code Q RX RZ) (p : Pauli Q) :
    centralizer C p ↔ (∀ r, dot (C.X r) p.2=0) ∧ (∀ s, dot (C.Z s) p.1=0) := by
  constructor
  · intro hp
    constructor
    · intro r
      have h := hp (C.X r,0) ⟨rowspace_row _ r,rowspace_zero _⟩
      simpa [symp,dot] using h
    · intro s
      have h := hp (0,C.Z s) ⟨rowspace_zero _,rowspace_row _ s⟩
      simpa [symp,dot] using h
  · rintro ⟨hx,hz⟩ ⟨x,z⟩ ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩
    simp [symp,dot_synth,hx,hz]

theorem isotropic (C : Code Q RX RZ) :
    ∀ s t : Pauli Q, s ∈ stabilizer C → t ∈ stabilizer C → symp s t=0 := by
  rintro ⟨x,z⟩ ⟨x',z'⟩ ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩ ⟨⟨a',rfl⟩,⟨b',rfl⟩⟩
  have h (a : RX → F₂) (b : RZ → F₂) : dot (synth C.X a) (synth C.Z b)=0 := by
    rw [dot_synth]
    apply Finset.sum_eq_zero
    intro r _
    rw [dot_comm,dot_synth]
    have hz : (∑ s : RZ,b s * dot (C.Z s) (C.X r))=0 := by
      apply Finset.sum_eq_zero
      intro s _
      rw [dot_comm,C.orthogonal]
      simp
    rw [hz,mul_zero]
  simp [symp,h,dot_comm (synth C.Z _) (synth C.X _)]

end BinaryCSS
