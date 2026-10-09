import Tanner

namespace BinaryCSS
variable {Q RX RZ : Type*} [Fintype Q] [Fintype RX] [Fintype RZ]
def rowDegree (C : Code Q RX RZ) (r : RX ⊕ RZ) : ℕ :=
  ∑ q,if combinedCheck C r q≠0 then 1 else 0
def colDegree (C : Code Q RX RZ) (q : Q) : ℕ :=
  ∑ r : RX ⊕ RZ,if combinedCheck C r q≠0 then 1 else 0

theorem rowDegree_card [DecidableEq Q] (C : Code Q RX RZ) (r : RX ⊕ RZ) :
    rowDegree C r=(Finset.univ.filter (fun q => combinedCheck C r q≠0)).card := by
  simp only [rowDegree,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem colDegree_card [DecidableEq (RX ⊕ RZ)] (C : Code Q RX RZ) (q : Q) :
    colDegree C q=(Finset.univ.filter (fun r : RX ⊕ RZ => combinedCheck C r q≠0)).card := by
  simp only [colDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
end BinaryCSS

namespace Shor
theorem row_degree_bound : ∀ r : Fin 4 ⊕ (Fin 5 × Fin 4),BinaryCSS.rowDegree code r≤10 := by decide
theorem col_degree_bound : ∀ q : Q,BinaryCSS.colDegree code q≤4 := by decide
end Shor

namespace ShorFamily
theorem diagonal_row_degree {R : Type*} (m : ℕ) (H : R → Shor.W) (r : Fin m × R) :
    (∑ q : Q m,if diagonal m H r q≠0 then 1 else 0)=
      ∑ q : Shor.Q,if H r.2 q≠0 then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  have hi : ∀ b : Fin m,(∑ q : Shor.Q,if diagonal m H r (b,q)≠0 then 1 else 0)=
      if r.1=b then ∑ q : Shor.Q,if H r.2 q≠0 then 1 else 0 else 0 := by
    intro b
    by_cases h : r.1=b <;> simp [diagonal,h]
  simp_rw [hi]
  simp

theorem diagonal_col_degree {R : Type*} [Fintype R] (m : ℕ) (H : R → Shor.W) (q : Q m) :
    (∑ r : Fin m × R,if diagonal m H r q≠0 then 1 else 0)=
      ∑ r : R,if H r q.2≠0 then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  have hi : ∀ b : Fin m,(∑ r : R,if diagonal m H (b,r) q≠0 then 1 else 0)=
      if b=q.1 then ∑ r : R,if H r q.2≠0 then 1 else 0 else 0 := by
    intro b
    by_cases h : b=q.1 <;> simp [diagonal,h]
  simp_rw [hi]
  simp

theorem row_degree_bound (m : ℕ) (r : RX m ⊕ RZ m) : BinaryCSS.rowDegree (code m) r≤10 := by
  cases r with
  | inl r =>
    change (∑ q : Q m,if diagonal m Shor.X r q≠0 then 1 else 0)≤10
    rw [diagonal_row_degree]
    exact Shor.row_degree_bound (.inl r.2)
  | inr r =>
    change (∑ q : Q m,if diagonal m Shor.Z r q≠0 then 1 else 0)≤10
    rw [diagonal_row_degree]
    exact Shor.row_degree_bound (.inr r.2)

theorem col_degree_bound (m : ℕ) (q : Q m) : BinaryCSS.colDegree (code m) q≤4 := by
  unfold BinaryCSS.colDegree
  rw [Fintype.sum_sum_type]
  change (∑ r : RX m,if diagonal m Shor.X r q≠0 then 1 else 0)+
    (∑ r : RZ m,if diagonal m Shor.Z r q≠0 then 1 else 0)≤4
  rw [diagonal_col_degree,diagonal_col_degree]
  convert Shor.col_degree_bound q.2 using 1
  simp only [BinaryCSS.colDegree,Fintype.sum_sum_type,BinaryCSS.combinedCheck,Shor.code]
  congr 1

theorem qubit_card (m : ℕ) : Fintype.card (Q m)=25*m := by simp [Q,Shor.Q,Nat.mul_comm]
theorem unbounded_length (N : ℕ) : ∃ n : ℕ,N<Fintype.card (Q (n+1)) := by
  refine ⟨N,?_⟩
  rw [qubit_card]
  omega
end ShorFamily
