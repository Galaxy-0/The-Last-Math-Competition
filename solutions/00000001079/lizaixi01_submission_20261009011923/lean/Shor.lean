import CSS
import Local
import Mathlib.Data.Fintype.Prod

namespace Shor
abbrev Q := Fin 5 × Fin 5
abbrev W := Q → F₂
abbrev P := W × W
def X (i : Fin 4) (q : Q) : F₂ := E i q.1
def Z (r : Fin 5 × Fin 4) (q : Q) : F₂ := if r.1=q.1 then E r.2 q.2 else 0
def block (x : W) (b : Fin 5) : V := fun j => x (b,j)
def blockParity (x : W) : V := fun b => parity (block x b)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 3000000 in
theorem orthogonal : ∀ i r,BinaryCSS.dot (X i) (Z r)=0 := by decide

def code : BinaryCSS.Code Q (Fin 4) (Fin 5 × Fin 4) where
  X := X
  Z := Z
  orthogonal := orthogonal

theorem X_rowspace (x : W) : BinaryCSS.rowspace X x ↔
    ∃ v : V,parity v=0 ∧ ∀ b j,x (b,j)=v b := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨synthE a,(parity_span _).mpr ⟨a,rfl⟩,fun b j => rfl⟩
  · rintro ⟨v,hv,hx⟩
    obtain ⟨a,ha⟩ := (parity_span v).mp hv
    refine ⟨a,?_⟩
    funext q
    obtain ⟨b,j⟩ := q
    change synthE a b=x (b,j)
    rw [ha,hx b j]

theorem Z_synth_block (a : (Fin 5 × Fin 4) → F₂) (b : Fin 5) :
    block (BinaryCSS.synth Z a) b = synthE (fun i => a (b,i)) := by
  ext j
  change (∑ r : Fin 5 × Fin 4,a r * Z r (b,j)) = _
  rw [Fintype.sum_prod_type]
  have hi : ∀ c : Fin 5,(∑ i : Fin 4,a (c,i) * Z (c,i) (b,j)) =
      if c=b then ∑ i : Fin 4,a (c,i) * E i j else 0 := by
    intro c
    by_cases h : c=b <;> simp [Z,h]
  simp_rw [hi]
  simp [synthE]

theorem Z_rowspace (x : W) : BinaryCSS.rowspace Z x ↔ ∀ b : Fin 5,parity (block x b)=0 := by
  classical
  constructor
  · rintro ⟨a,rfl⟩ b
    apply (parity_span _).mpr
    exact ⟨(fun i => a (b,i)),(Z_synth_block a b).symm⟩
  · intro hx
    have he : ∀ b : Fin 5,∃ a : A,synthE a=block x b := fun b => (parity_span _).mp (hx b)
    choose a ha using he
    refine ⟨(fun r => a r.1 r.2),?_⟩
    funext q
    obtain ⟨b,j⟩ := q
    have h := congrFun (Z_synth_block (fun r => a r.1 r.2) b) j
    simpa [block,ha b] using h

theorem stabilizer_iff (p : P) : p ∈ BinaryCSS.stabilizer code ↔
    (∃ v : V,parity v=0 ∧ ∀ b j,p.1 (b,j)=v b) ∧
    (∀ b : Fin 5,parity (block p.2 b)=0) := by
  change (BinaryCSS.rowspace X p.1 ∧ BinaryCSS.rowspace Z p.2) ↔ _
  rw [X_rowspace,Z_rowspace]

theorem dot_X (i : Fin 4) (z : W) : BinaryCSS.dot (X i) z = adjDot i (blockParity z) := by
  simp only [BinaryCSS.dot,X,Fintype.sum_prod_type,adjDot,blockParity,parity,block,
    Finset.mul_sum]

theorem dot_Z (r : Fin 5 × Fin 4) (x : W) : BinaryCSS.dot (Z r) x = adjDot r.2 (block x r.1) := by
  unfold BinaryCSS.dot
  rw [Fintype.sum_prod_type]
  have hi : ∀ b : Fin 5,(∑ j : Fin 5,Z r (b,j) * x (b,j)) =
      if r.1=b then ∑ j : Fin 5,E r.2 j * x (b,j) else 0 := by
    intro b
    by_cases h : r.1=b <;> simp [Z,h]
  simp_rw [hi]
  simp [adjDot,block]

theorem centralizer_iff (p : P) : BinaryCSS.centralizer code p ↔
    (∃ v : V,∀ b j,p.1 (b,j)=v b) ∧
    (∃ t : F₂,∀ b : Fin 5,parity (block p.2 b)=t) := by
  classical
  rw [BinaryCSS.centralizer_iff]
  change ((∀ i : Fin 4,BinaryCSS.dot (X i) p.2=0) ∧
    (∀ r : Fin 5 × Fin 4,BinaryCSS.dot (Z r) p.1=0)) ↔ _
  simp_rw [dot_X,dot_Z]
  constructor
  · rintro ⟨hz,hx⟩
    have he : ∀ b : Fin 5,∃ t : F₂,∀ j : Fin 5,p.1 (b,j)=t :=
      fun b => (adjacent_constant (block p.1 b)).mp (fun i => hx (b,i))
    choose v hv using he
    exact ⟨⟨v,hv⟩,(adjacent_constant (blockParity p.2)).mp hz⟩
  · rintro ⟨⟨v,hv⟩,⟨t,ht⟩⟩
    constructor
    · exact (adjacent_constant (blockParity p.2)).mpr ⟨t,ht⟩
    · intro r
      exact ((adjacent_constant (block p.1 r.1)).mpr ⟨v r.1,hv r.1⟩) r.2

theorem support_injection (p : P) (f : Fin 5 → Q)
    (hs : ∀ j,p.1 (f j)≠0 ∨ p.2 (f j)≠0) (hf : Function.Injective f) :
    5 ≤ BinaryCSS.sweight p := by
  classical
  have h : (Finset.univ : Finset (Fin 5)).card ≤
      (Finset.univ.filter (fun q => p.1 q≠0 ∨ p.2 q≠0)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro j hj
      simp [hs j]
    · intro j hj k hk h
      exact hf h
  simpa [BinaryCSS.sweight] using h

theorem logical_lower (p : P) (hp : BinaryCSS.logical code p) : 5 ≤ BinaryCSS.sweight p := by
  classical
  obtain ⟨⟨v,hv⟩,⟨t,ht⟩⟩ := (centralizer_iff p).mp hp.1
  by_cases hx : ∃ b : Fin 5,v b≠0
  · obtain ⟨b,hb⟩ := hx
    apply support_injection p (fun j => (b,j))
    · intro j
      exact Or.inl (by simpa [hv b j] using hb)
    · intro j k h
      exact (Prod.mk.inj h).2
  · have vz : ∀ b,v b=0 := by simpa using hx
    have tn : t≠0 := by
      intro tz
      apply hp.2
      apply (stabilizer_iff p).mpr
      exact ⟨⟨v,by simp [parity,vz],hv⟩,fun b => (ht b).trans tz⟩
    have he : ∀ b : Fin 5,∃ j : Fin 5,p.2 (b,j)≠0 := by
      intro b
      apply nonzero_of_parity
      change parity (block p.2 b)≠0
      rw [ht b]
      exact tn
    choose j hj using he
    apply support_injection p (fun b => (b,j b))
    · intro b
      exact Or.inr (hj b)
    · intro b c h
      exact (Prod.mk.inj h).1

def witnessX (q : Q) : F₂ := if q.1=0 then 1 else 0
def witness : P := (witnessX,0)
theorem witness_logical : BinaryCSS.logical code witness := by
  constructor
  · apply (centralizer_iff _).mpr
    refine ⟨⟨(fun b => if b=0 then 1 else 0),fun b j => rfl⟩,⟨0,?_⟩⟩
    intro b
    simp [witness,block,parity]
  · intro hs
    obtain ⟨⟨v,hv,hx⟩,hz⟩ := (stabilizer_iff _).mp hs
    have he : v=(fun b : Fin 5 => if b=0 then 1 else 0) := by
      funext b
      exact (hx b 0).symm
    rw [he,parity_basis] at hv
    exact one_ne_zero hv

theorem witness_weight : BinaryCSS.sweight witness=5 := by decide
theorem quantum_distance_five : BinaryCSS.HasQuantumDistance code 5 :=
  ⟨⟨witness,witness_logical,witness_weight⟩,logical_lower⟩
end Shor
