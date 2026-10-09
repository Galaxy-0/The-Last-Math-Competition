import Shor

namespace ShorFamily
open Shor
abbrev Q (m : ℕ) := Fin m × Shor.Q
abbrev RX (m : ℕ) := Fin m × Fin 4
abbrev RZ (m : ℕ) := Fin m × (Fin 5 × Fin 4)
abbrev W (m : ℕ) := Q m → F₂
abbrev P (m : ℕ) := W m × W m

def diagonal {R : Type*} (m : ℕ) (H : R → Shor.W) (r : Fin m × R) (q : Q m) : F₂ :=
  if r.1=q.1 then H r.2 q.2 else 0

def code (m : ℕ) : BinaryCSS.Code (Q m) (RX m) (RZ m) where
  X := diagonal m Shor.X
  Z := diagonal m Shor.Z
  orthogonal := by
    intro r s
    unfold BinaryCSS.dot
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hr : r.1=b
    · by_cases hs : s.1=b
      · simpa [diagonal,hr,hs,BinaryCSS.dot] using Shor.orthogonal r.2 s.2
      · simp [diagonal,hr,hs]
    · simp [diagonal,hr]

def block {m : ℕ} (x : W m) (b : Fin m) : Shor.W := fun q => x (b,q)
def blockPauli {m : ℕ} (p : P m) (b : Fin m) : Shor.P := (block p.1 b,block p.2 b)

theorem diagonal_synth {R : Type*} [Fintype R] (m : ℕ) (H : R → Shor.W)
    (a : (Fin m × R) → F₂) (b : Fin m) :
    block (BinaryCSS.synth (diagonal m H) a) b = BinaryCSS.synth H (fun r => a (b,r)) := by
  ext q
  change (∑ r : Fin m × R,a r * diagonal m H r (b,q)) = _
  rw [Fintype.sum_prod_type]
  have hi : ∀ c : Fin m,(∑ r : R,a (c,r) * diagonal m H (c,r) (b,q)) =
      if c=b then ∑ r : R,a (c,r) * H r q else 0 := by
    intro c
    by_cases h : c=b <;> simp [diagonal,h]
  simp_rw [hi]
  simp [BinaryCSS.synth]

theorem diagonal_rowspace {R : Type*} [Fintype R] (m : ℕ) (H : R → Shor.W) (x : W m) :
    BinaryCSS.rowspace (diagonal m H) x ↔ ∀ b : Fin m,BinaryCSS.rowspace H (block x b) := by
  classical
  constructor
  · rintro ⟨a,rfl⟩ b
    exact ⟨(fun r => a (b,r)),(diagonal_synth m H a b).symm⟩
  · intro hx
    choose a ha using hx
    refine ⟨(fun r => a r.1 r.2),?_⟩
    funext q
    obtain ⟨b,j⟩ := q
    have h := congrFun (diagonal_synth m H (fun r => a r.1 r.2) b) j
    simpa [block,ha b] using h

theorem stabilizer_blocks (m : ℕ) (p : P m) :
    p ∈ BinaryCSS.stabilizer (code m) ↔ ∀ b : Fin m,blockPauli p b ∈ BinaryCSS.stabilizer Shor.code := by
  change (BinaryCSS.rowspace (diagonal m Shor.X) p.1 ∧
    BinaryCSS.rowspace (diagonal m Shor.Z) p.2) ↔ _
  rw [diagonal_rowspace,diagonal_rowspace]
  change ((∀ b,BinaryCSS.rowspace Shor.X (block p.1 b)) ∧
    (∀ b,BinaryCSS.rowspace Shor.Z (block p.2 b))) ↔
    ∀ b,(BinaryCSS.rowspace Shor.X (block p.1 b) ∧ BinaryCSS.rowspace Shor.Z (block p.2 b))
  exact forall_and.symm

theorem diagonal_dot {R : Type*} (m : ℕ) (H : R → Shor.W) (r : Fin m × R) (x : W m) :
    BinaryCSS.dot (diagonal m H r) x = BinaryCSS.dot (H r.2) (block x r.1) := by
  unfold BinaryCSS.dot
  rw [Fintype.sum_prod_type]
  have hi : ∀ b : Fin m,(∑ q : Shor.Q,diagonal m H r (b,q) * x (b,q)) =
      if r.1=b then ∑ q : Shor.Q,H r.2 q * x (b,q) else 0 := by
    intro b
    by_cases h : r.1=b <;> simp [diagonal,h]
  simp_rw [hi]
  simp [block]

theorem centralizer_blocks (m : ℕ) (p : P m) :
    BinaryCSS.centralizer (code m) p ↔ ∀ b : Fin m,BinaryCSS.centralizer Shor.code (blockPauli p b) := by
  rw [BinaryCSS.centralizer_iff]
  change ((∀ r : RX m,BinaryCSS.dot (diagonal m Shor.X r) p.2=0) ∧
    (∀ r : RZ m,BinaryCSS.dot (diagonal m Shor.Z r) p.1=0)) ↔ _
  simp_rw [diagonal_dot]
  constructor
  · rintro ⟨hx,hz⟩ b
    exact (BinaryCSS.centralizer_iff Shor.code _).mpr ⟨fun r => hx (b,r),fun r => hz (b,r)⟩
  · intro hp
    constructor
    · intro r
      exact ((BinaryCSS.centralizer_iff Shor.code _).mp (hp r.1)).1 r.2
    · intro r
      exact ((BinaryCSS.centralizer_iff Shor.code _).mp (hp r.1)).2 r.2

theorem logical_block (m : ℕ) (p : P m) (hp : BinaryCSS.logical (code m) p) :
    ∃ b : Fin m,BinaryCSS.logical Shor.code (blockPauli p b) := by
  classical
  have hc := (centralizer_blocks m p).mp hp.1
  have hn : ¬ ∀ b : Fin m,blockPauli p b ∈ BinaryCSS.stabilizer Shor.code := by
    intro hs
    exact hp.2 ((stabilizer_blocks m p).mpr hs)
  obtain ⟨b,hb⟩ := not_forall.mp hn
  exact ⟨b,hc b,hb⟩

theorem block_weight_le (m : ℕ) (p : P m) (b : Fin m) :
    BinaryCSS.sweight (blockPauli p b) ≤ BinaryCSS.sweight p := by
  classical
  unfold BinaryCSS.sweight
  apply Finset.card_le_card_of_injOn (fun q => (b,q))
  · intro q hq
    have hs := (Finset.mem_filter.mp hq).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩
  · intro q hq r hr h
    exact (Prod.mk.inj h).2

theorem logical_lower (m : ℕ) (p : P m) (hp : BinaryCSS.logical (code m) p) :
    5 ≤ BinaryCSS.sweight p := by
  obtain ⟨b,hb⟩ := logical_block m p hp
  exact (Shor.logical_lower _ hb).trans (block_weight_le m p b)

def supported (m : ℕ) (b : Fin m) (x : Shor.W) : W m :=
  fun q => if q.1=b then x q.2 else 0
def witness (m : ℕ) (b : Fin m) : P m := (supported m b Shor.witness.1,supported m b Shor.witness.2)

theorem supported_block (m : ℕ) (b c : Fin m) (x : Shor.W) :
    block (supported m b x) c = if c=b then x else 0 := by
  ext q
  by_cases h : c=b <;> simp [block,supported,h]

theorem witness_logical (m : ℕ) (b : Fin m) : BinaryCSS.logical (code m) (witness m b) := by
  constructor
  · apply (centralizer_blocks m _).mpr
    intro c
    change BinaryCSS.centralizer Shor.code
      (block (supported m b Shor.witness.1) c,block (supported m b Shor.witness.2) c)
    rw [supported_block,supported_block]
    by_cases h : c=b
    · simpa [h] using Shor.witness_logical.1
    · simp only [h,ite_false]
      apply (BinaryCSS.centralizer_iff _ _).mpr
      simp [BinaryCSS.dot]
  · intro hs
    have hb := (stabilizer_blocks m _).mp hs b
    change (block (supported m b Shor.witness.1) b,block (supported m b Shor.witness.2) b)
      ∈ BinaryCSS.stabilizer Shor.code at hb
    rw [supported_block,supported_block] at hb
    exact Shor.witness_logical.2 (by simpa using hb)

theorem witness_weight (m : ℕ) (b : Fin m) : BinaryCSS.sweight (witness m b)=5 := by
  classical
  unfold BinaryCSS.sweight
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  have hi : ∀ c : Fin m,(∑ q : Shor.Q,if (witness m b).1 (c,q)≠0 ∨
      (witness m b).2 (c,q)≠0 then 1 else 0) =
      if c=b then BinaryCSS.sweight Shor.witness else 0 := by
    intro c
    by_cases h : c=b
    · simp only [witness,supported,h,ite_true,Prod.fst,Prod.snd]
      simp only [BinaryCSS.sweight,Finset.card_eq_sum_ones,Finset.sum_filter]
    · simp [witness,supported,h]
  simp_rw [hi]
  simp [Shor.witness_weight]

theorem quantum_distance_five (m : ℕ) (hm : 0<m) : BinaryCSS.HasQuantumDistance (code m) 5 := by
  let b : Fin m := ⟨0,hm⟩
  exact ⟨⟨witness m b,witness_logical m b,witness_weight m b⟩,logical_lower m⟩
end ShorFamily
