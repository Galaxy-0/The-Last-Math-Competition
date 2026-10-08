import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
open scoped Matrix ComplexOrder
namespace RenyiDephasing
abbrev M := Matrix (Fin 2) (Fin 2) ℂ
abbrev Superoperator := M →ₗ[ℂ] M

def dephase : Superoperator where
  toFun X := Matrix.diagonal (fun i => X i i)
  map_add' X Y := by ext i j; simp [Matrix.diagonal]; split_ifs <;> simp
  map_smul' c X := by ext i j; simp [Matrix.diagonal]

def amplify (n : ℕ) (Phi : Superoperator)
    (X : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  fun i j => Phi (fun a b => X (i.1,a) (j.1,b)) i.2 j.2

def IsChannel (Phi : Superoperator) : Prop :=
  (∀ n X, X.PosSemidef → (amplify n Phi X).PosSemidef) ∧
  (∀ X, Matrix.trace (Phi X)=Matrix.trace X)

def blockProjector (n : ℕ) (a : Fin 2) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i.2=a then 1 else 0)

theorem amplification_kraus (n : ℕ)
    (X : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) :
    amplify n dephase X = (blockProjector n 0)ᴴ*X*blockProjector n 0 +
      (blockProjector n 1)ᴴ*X*blockProjector n 1 := by
  simp only [blockProjector, Matrix.diagonal_conjTranspose]
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  all_goals simp [amplify, dephase, Matrix.diagonal]

theorem dephase_channel : IsChannel dephase := by
  constructor
  · intro n X hX
    rw [amplification_kraus]
    exact (hX.conjTranspose_mul_mul_same _).add (hX.conjTranspose_mul_mul_same _)
  · intro X
    simp [dephase, Matrix.trace]

def rho : M := Matrix.diagonal ![9/25,16/25]
def sigma : M := Matrix.diagonal ![16/25,9/25]
def rootRho : M := Matrix.diagonal ![3/5,4/5]
def rootSigma : M := Matrix.diagonal ![4/5,3/5]
def Density (X : M) : Prop := X.PosSemidef ∧ Matrix.trace X=1

theorem rho_positive : rho.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i; fin_cases i <;> dsimp <;> rw [RCLike.nonneg_iff] <;> norm_num
theorem sigma_positive : sigma.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i; fin_cases i <;> dsimp <;> rw [RCLike.nonneg_iff] <;> norm_num
theorem states_density : Density rho ∧ Density sigma := by
  exact ⟨⟨rho_positive, by norm_num [rho, Matrix.trace, Fin.sum_univ_two]⟩,
    ⟨sigma_positive, by norm_num [sigma, Matrix.trace, Fin.sum_univ_two]⟩⟩

theorem states_full_rank : rho.det ≠ 0 ∧ sigma.det ≠ 0 := by
  norm_num [rho, sigma, Matrix.det_fin_two]
theorem states_distinct : rho ≠ sigma := by
  intro h
  have := congrArg (fun X : M => X 0 0) h
  norm_num [rho,sigma] at this

theorem fixes_states : dephase rho=rho ∧ dephase sigma=sigma := by
  simp [dephase, rho, sigma]

/-- Canonical positive square root on its genuine positive domain. -/
def positiveRoot (X : M) : M := by
  classical
  exact if h : X.PosSemidef then h.sqrt else 0
def petzHalf (X Y : M) : ℝ := -2*Real.log ((Matrix.trace (positiveRoot X*positiveRoot Y)).re)

theorem root_rho : positiveRoot rho=rootRho := by
  rw [positiveRoot, dif_pos rho_positive]
  symm
  apply Matrix.PosSemidef.eq_sqrt_of_sq_eq (B:=rho)
  · apply Matrix.PosSemidef.diagonal
    intro i; fin_cases i <;> dsimp <;> rw [RCLike.nonneg_iff] <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [rootRho,rho,pow_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal]

theorem root_sigma : positiveRoot sigma=rootSigma := by
  rw [positiveRoot, dif_pos sigma_positive]
  symm
  apply Matrix.PosSemidef.eq_sqrt_of_sq_eq (B:=sigma)
  · apply Matrix.PosSemidef.diagonal
    intro i; fin_cases i <;> dsimp <;> rw [RCLike.nonneg_iff] <;> norm_num
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [rootSigma,sigma,pow_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal]

theorem overlap_exact : (Matrix.trace (positiveRoot rho*positiveRoot sigma)).re=24/25 := by
  rw [root_rho,root_sigma]
  norm_num [rootRho,rootSigma,Matrix.trace,Matrix.diagonal_mul_diagonal,Fin.sum_univ_two]

theorem divergence_exact : petzHalf rho sigma = -2*Real.log (24/25) := by
  rw [petzHalf,overlap_exact]
theorem divergence_positive : 0 < petzHalf rho sigma := by
  rw [divergence_exact]
  have := Real.log_neg (by norm_num : (0:ℝ)<24/25) (by norm_num : (24/25:ℝ)<1)
  linarith
theorem equality_case : petzHalf (dephase rho) (dephase sigma)=petzHalf rho sigma := by
  rw [fixes_states.1,fixes_states.2]

def J : M := !![0,1;0,0]
theorem killed_nonzero : dephase J=0 ∧ J≠0 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [dephase,J,Matrix.diagonal]
  · intro h
    have := congrArg (fun X : M => X 0 1) h
    norm_num [J] at this

theorem dephase_not_injective : ¬ Function.Injective dephase := by
  intro h
  exact killed_nonzero.2 (h (by simpa using killed_nonzero.1))

def UnitaryConjugation (Phi : Superoperator) : Prop :=
  ∃ U : M, Uᴴ*U=1 ∧ U*Uᴴ=1 ∧ ∀ X, Phi X=U*X*Uᴴ

theorem unitary_injective (Phi : Superoperator) (h : UnitaryConjugation Phi) :
    Function.Injective Phi := by
  obtain ⟨U,hU,_,hPhi⟩ := h
  intro X Y hXY
  rw [hPhi,hPhi] at hXY
  have h := congrArg (fun Z : M => Uᴴ*Z*U) hXY
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul] at h
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one] at h
  simpa only [← Matrix.mul_assoc, hU, Matrix.one_mul] using h

theorem not_unitary : ¬ UnitaryConjugation dephase := by
  intro h
  exact dephase_not_injective (unitary_injective _ h)

theorem sigma_surjective : Function.Surjective (fun x : Fin 2 → ℂ => sigma*ᵥx) := by
  intro v
  refine ⟨![25/16*v 0,25/9*v 1],?_⟩
  ext i; fin_cases i <;> simp [sigma,Matrix.mulVec_diagonal] <;> ring

theorem sigma_full_support : Set.range (fun x : Fin 2 → ℂ => sigma*ᵥx)=Set.univ :=
  Set.range_eq_univ.mpr sigma_surjective

/-- All output-state ranges being contained in a single line is a necessary
condition for collapse to a one-dimensional output space. -/
def OneDimensionalOutput (Phi : Superoperator) : Prop :=
  ∃ v : Fin 2 → ℂ, ∀ X, Density X → ∀ x, ∃ c : ℂ, (Phi X)*ᵥx=c • v

theorem not_one_dimensional : ¬ OneDimensionalOutput dephase := by
  rintro ⟨v,h⟩
  have hall : ∀ w : Fin 2 → ℂ, ∃ c : ℂ, w=c • v := by
    intro w
    obtain ⟨x,hx⟩ := sigma_surjective w
    change sigma*ᵥx=w at hx
    obtain ⟨c,hc⟩ := h sigma states_density.2 x
    rw [fixes_states.2,hx] at hc
    exact ⟨c,hc⟩
  obtain ⟨a,ha⟩ := hall ![1,0]
  obtain ⟨b,hb⟩ := hall ![0,1]
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have hb1 := congrFun hb 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Pi.smul_apply,smul_eq_mul] at ha0 ha1 hb1
  have ha_ne : a≠0 := by intro he; simp [he] at ha0
  have hv : v 1=0 := (mul_eq_zero.mp ha1.symm).resolve_left ha_ne
  simp [hv] at hb1

theorem counterexample : IsChannel dephase ∧ Density rho ∧ Density sigma ∧
    rho≠sigma ∧ rho.det≠0 ∧ sigma.det≠0 ∧ 0<petzHalf rho sigma ∧
    petzHalf (dephase rho) (dephase sigma)=petzHalf rho sigma ∧
    ¬ UnitaryConjugation dephase ∧ ¬ OneDimensionalOutput dephase :=
  ⟨dephase_channel,states_density.1,states_density.2,states_distinct,
    states_full_rank.1,states_full_rank.2,divergence_positive,equality_case,
    not_unitary,not_one_dimensional⟩

#print axioms amplification_kraus
#print axioms dephase_channel
#print axioms states_density
#print axioms states_full_rank
#print axioms root_rho
#print axioms root_sigma
#print axioms overlap_exact
#print axioms divergence_positive
#print axioms equality_case
#print axioms not_unitary
#print axioms sigma_full_support
#print axioms not_one_dimensional
#print axioms counterexample
end RenyiDephasing
