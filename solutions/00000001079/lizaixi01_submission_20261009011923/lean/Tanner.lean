import Copies
import Mathlib.Combinatorics.SimpleGraph.Girth

namespace BinaryCSS
variable {Q RX RZ : Type*} [Fintype Q]
def combinedCheck (C : Code Q RX RZ) : RX ⊕ RZ → Word Q
  | .inl r => C.X r
  | .inr s => C.Z s
abbrev Vertex (Q RX RZ : Type*) := (RX ⊕ RZ) ⊕ Q
def incidence (C : Code Q RX RZ) : Vertex Q RX RZ → Vertex Q RX RZ → Prop
  | .inl r,.inr q => combinedCheck C r q≠0
  | .inr q,.inl r => combinedCheck C r q≠0
  | _,_ => False
def tanner (C : Code Q RX RZ) : SimpleGraph (Vertex Q RX RZ) where
  Adj := incidence C
  symm := ⟨by intro a b; cases a <;> cases b <;> simp [incidence]⟩
  loopless := ⟨by intro a; cases a <;> simp [incidence]⟩
instance (C : Code Q RX RZ) : DecidableRel (tanner C).Adj := fun a b => by
  cases a <;> cases b <;> dsimp [tanner,incidence] <;> infer_instance

theorem no_triangle (C : Code Q RX RZ) : ∀ a b c : Vertex Q RX RZ,
    ¬ ((tanner C).Adj a b ∧ (tanner C).Adj b c ∧ (tanner C).Adj c a) := by
  intro a b c
  cases a <;> cases b <;> cases c <;> simp [tanner,incidence]

theorem no_length_three (C : Code Q RX RZ) (a : Vertex Q RX RZ)
    (w : (tanner C).Walk a a) : w.length≠3 := by
  intro hw
  cases w with
  | nil => simp at hw
  | @cons a b a hab p =>
    cases p with
    | nil => simp at hw
    | @cons b c a hbc q =>
      cases q with
      | nil => simp at hw
      | @cons c d a hcd r =>
        cases r with
        | nil => exact no_triangle C a b c ⟨hab,hbc,hcd⟩
        | cons h s => simp only [SimpleGraph.Walk.length_cons] at hw; omega

theorem girth_four_of_cycle (C : Code Q RX RZ) (a : Vertex Q RX RZ)
    (w : (tanner C).Walk a a) (hw : w.IsCycle) (hl : w.length=4) : (tanner C).girth=4 := by
  have hn : ¬ (tanner C).IsAcyclic := fun ha => ha w hw
  have hu : (tanner C).girth≤4 := by simpa [hl] using (tanner C).girth_le_length hw
  have hlower := (tanner C).three_le_girth hn
  obtain ⟨b,p,hp,he⟩ := SimpleGraph.exists_girth_eq_length.mpr hn
  have hne : (tanner C).girth≠3 := by rw [he]; exact no_length_three C b p
  omega
end BinaryCSS

namespace ShorFamily
def first (m : ℕ) (hm : 0<m) : Fin m := ⟨0,hm⟩
def check0 (m : ℕ) (hm : 0<m) : BinaryCSS.Vertex (Q m) (RX m) (RZ m) :=
  .inl (.inl (first m hm,0))
def check1 (m : ℕ) (hm : 0<m) : BinaryCSS.Vertex (Q m) (RX m) (RZ m) :=
  .inl (.inl (first m hm,1))
def qubit0 (m : ℕ) (hm : 0<m) : BinaryCSS.Vertex (Q m) (RX m) (RZ m) :=
  .inr (first m hm,(1,0))
def qubit1 (m : ℕ) (hm : 0<m) : BinaryCSS.Vertex (Q m) (RX m) (RZ m) :=
  .inr (first m hm,(1,1))

def cycle4 (m : ℕ) (hm : 0<m) : (BinaryCSS.tanner (code m)).Walk (check0 m hm) (check0 m hm) :=
  .cons (by simp [BinaryCSS.tanner,BinaryCSS.incidence,BinaryCSS.combinedCheck,code,diagonal,check0,check1,qubit0,qubit1,first,Shor.X,Shor.E] : (BinaryCSS.tanner (code m)).Adj (check0 m hm) (qubit0 m hm))
  (.cons (by simp [BinaryCSS.tanner,BinaryCSS.incidence,BinaryCSS.combinedCheck,code,diagonal,check0,check1,qubit0,qubit1,first,Shor.X,Shor.E] : (BinaryCSS.tanner (code m)).Adj (qubit0 m hm) (check1 m hm))
  (.cons (by simp [BinaryCSS.tanner,BinaryCSS.incidence,BinaryCSS.combinedCheck,code,diagonal,check0,check1,qubit0,qubit1,first,Shor.X,Shor.E] : (BinaryCSS.tanner (code m)).Adj (check1 m hm) (qubit1 m hm))
  (.cons (by simp [BinaryCSS.tanner,BinaryCSS.incidence,BinaryCSS.combinedCheck,code,diagonal,check0,check1,qubit0,qubit1,first,Shor.X,Shor.E] : (BinaryCSS.tanner (code m)).Adj (qubit1 m hm) (check0 m hm)) .nil)))

theorem cycle4_isCycle (m : ℕ) (hm : 0<m) : (cycle4 m hm).IsCycle := by
  apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · apply SimpleGraph.Walk.IsPath.mk'
    simp [cycle4,SimpleGraph.Walk.tail,SimpleGraph.Walk.support,SimpleGraph.Walk.length,
      check0,check1,qubit0,qubit1,first]
  · simp [cycle4,SimpleGraph.Walk.length]

theorem girth_four (m : ℕ) (hm : 0<m) : (BinaryCSS.tanner (code m)).girth=4 :=
  BinaryCSS.girth_four_of_cycle (code m) (check0 m hm) (cycle4 m hm) (cycle4_isCycle m hm) rfl
end ShorFamily
