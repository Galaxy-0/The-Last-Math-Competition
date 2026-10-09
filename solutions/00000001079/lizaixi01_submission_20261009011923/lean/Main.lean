import LDPC
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BinaryCSS
def IsLDPCFamily (Q RX RZ : ℕ → Type) [∀ n,Fintype (Q n)] [∀ n,Fintype (RX n)]
    [∀ n,Fintype (RZ n)] (C : ∀ n,Code (Q n) (RX n) (RZ n)) : Prop :=
  (∃ rowBound colBound : ℕ,(∀ n r,rowDegree (C n) r≤rowBound) ∧
    (∀ n q,colDegree (C n) q≤colBound)) ∧
  (∀ N : ℕ,∃ n : ℕ,N<Fintype.card (Q n))

def UniversalBound (L : ℝ → ℝ) : Prop :=
  ∀ (Q RX RZ : ℕ → Type) [∀ n,Fintype (Q n)] [∀ n,Fintype (RX n)] [∀ n,Fintype (RZ n)]
    (C : ∀ n,Code (Q n) (RX n) (RZ n)),IsLDPCFamily Q RX RZ C →
    ∀ n d,HasQuantumDistance (C n) d →
      (d : ℝ)/((tanner (C n)).girth : ℝ)≤L ((tanner (C n)).girth : ℝ)/2
end BinaryCSS

namespace ShorFamily
abbrev FamilyQ (n : ℕ) := Q (n+1)
abbrev FamilyRX (n : ℕ) := RX (n+1)
abbrev FamilyRZ (n : ℕ) := RZ (n+1)
def familyCode (n : ℕ) : BinaryCSS.Code (FamilyQ n) (FamilyRX n) (FamilyRZ n) := code (n+1)
instance familyQFinite : ∀ n,Fintype (FamilyQ n) := fun n => inferInstance
instance familyRXFinite : ∀ n,Fintype (FamilyRX n) := fun n => inferInstance
instance familyRZFinite : ∀ n,Fintype (FamilyRZ n) := fun n => inferInstance

theorem isLDPCFamily : BinaryCSS.IsLDPCFamily FamilyQ FamilyRX FamilyRZ familyCode :=
  ⟨⟨10,4,fun n r => row_degree_bound (n+1) r,fun n q => col_degree_bound (n+1) q⟩,
    unbounded_length⟩

theorem family_distance (n : ℕ) : BinaryCSS.HasQuantumDistance (familyCode n) 5 :=
  quantum_distance_five (n+1) (Nat.zero_lt_succ n)

theorem family_girth (n : ℕ) : (BinaryCSS.tanner (familyCode n)).girth=4 :=
  girth_four (n+1) (Nat.zero_lt_succ n)

theorem refute_bound (L : ℝ → ℝ) (hL : L 4≤2) : ¬ BinaryCSS.UniversalBound L := by
  intro h
  have hf := h FamilyQ FamilyRX FamilyRZ familyCode isLDPCFamily 0 5 (family_distance 0)
  rw [family_girth] at hf
  norm_num at hf
  linarith

theorem log_four : Real.log 4=2*Real.log 2 := by
  rw [show (4 : ℝ)=2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
  ring

theorem refute_natural : ¬ BinaryCSS.UniversalBound Real.log := by
  apply refute_bound
  rw [log_four]
  have h := Real.log_two_lt_d9
  linarith

theorem logb_four_le_two (b : ℝ) (hb : 2≤b) : Real.logb b 4≤2 := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2≤Real.log b := Real.log_le_log (by norm_num) hb
  have hp : 0<Real.log b := h2.trans_le hlog
  rw [Real.logb,div_le_iff₀ hp,log_four]
  linarith

theorem refute_base (b : ℝ) (hb : 2≤b) : ¬ BinaryCSS.UniversalBound (Real.logb b) :=
  refute_bound _ (logb_four_le_two b hb)

theorem refute_binary : ¬ BinaryCSS.UniversalBound (Real.logb 2) := refute_base 2 (by norm_num)

#print axioms BinaryCSS.stabilizer_eq_span
#print axioms Shor.quantum_distance_five
#print axioms ShorFamily.quantum_distance_five
#print axioms ShorFamily.girth_four
#print axioms ShorFamily.isLDPCFamily
#print axioms ShorFamily.refute_natural
#print axioms ShorFamily.refute_binary
#print axioms ShorFamily.refute_base
end ShorFamily
