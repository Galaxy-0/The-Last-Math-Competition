import Mathlib

/-!
# Conjecture 00000004780

Joint moments and operator-valued distributions are two layers of noncommutative invariants.
Conjecture: there exist two matrix models whose joint moments have identical asymptotics while
their operator-valued distributions differ, and the separation is realized by an explicit
rearrangement of the block structure.

We work with matrices in block form `M_2(M_N(ℂ)) = Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ`.

* Joint moments: the normalized trace `tr_{2N}(p(X_1, …, X_r))` of every noncommutative
  polynomial `p ∈ ℂ⟨x_1, …, x_r⟩` (`FreeAlgebra ℂ (Fin r)`).
* Operator-valued distribution over `B = M_2(ℂ)`: the `B`-valued moments
  `E_N(b_0 X_{i_1} b_1 ⋯ X_{i_m} b_m)`, where `b ∈ B` acts as `b ⊗ 1_N` and
  `E_N = id_2 ⊗ tr_N` is the block-wise normalized partial trace.
* Rearrangement of the block structure: conjugation by the block permutation
  `σ ⊗ 1_N`, i.e. `Matrix.reindex` along `σ × id`.

Main results:
* `rearrange_jointMoment`: any rearrangement of the blocks preserves every joint moment of
  every matrix model, for every `N`.
* `rearrange_condExp`: the rearrangement acts on block expectations by conjugation by `σ`.
* `conjecture4780`: an explicit pair of (deterministic, self-adjoint) matrix models, the second
  obtained from the first by swapping the two diagonal blocks, with identical joint moments for
  every `N` and every polynomial (with a common limit), but different `M_2(ℂ)`-valued
  distributions for every `N ≥ 1` (and different limits of the first `B`-valued moment).
-/

namespace Conjecture4780

open Matrix Filter Topology
open scoped Kronecker

/-- Normalized trace `tr = Tr / dim`. -/
noncomputable def ntr {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * M.trace

/-- Block matrices `M_2(M_N(ℂ))`. -/
abbrev BMat (N : ℕ) := Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℂ

/-- A matrix model of `r` matrices: for each size parameter `N`, an `r`-tuple in `M_2(M_N(ℂ))`. -/
abbrev Model (r : ℕ) := (N : ℕ) → Fin r → BMat N

/-- Evaluation of a noncommutative polynomial at a tuple of matrices. -/
noncomputable def eval {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Fin r → Matrix ι ι ℂ) :
    FreeAlgebra ℂ (Fin r) →ₐ[ℂ] Matrix ι ι ℂ :=
  FreeAlgebra.lift ℂ X

/-- The joint moment `tr_{2N}(p(X_N))` of the model `X` at level `N`. -/
noncomputable def jointMoment {r : ℕ} (X : Model r) (N : ℕ) (p : FreeAlgebra ℂ (Fin r)) : ℂ :=
  ntr (eval (X N) p)

/-- The block-wise normalized partial trace `E_N = id_2 ⊗ tr_N : M_2(M_N(ℂ)) → M_2(ℂ)`. For
`N ≥ 1` it is the `B`-valued conditional expectation; at `N = 0` it is the zero map (a formal
extension only). -/
noncomputable def condExp (N : ℕ) (M : BMat N) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (N : ℂ)⁻¹ * ∑ a : Fin N, M (i, a) (j, a)

/-- The map `b ↦ b ⊗ 1_N` from `B = M_2(ℂ)` to `M_2(M_N(ℂ))`; an embedding for `N ≥ 1`. -/
def emb (N : ℕ) (b : Matrix (Fin 2) (Fin 2) ℂ) : BMat N := b ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ)

/-- The `B`-valued moment `E_N(b_0 X_{i_1} b_1 ⋯ X_{i_m} b_m)` for `l = [(i_1,b_1), …, (i_m,b_m)]`.
The `B`-valued (operator-valued) distribution of `X` at level `N` is the map `(b_0, l) ↦ this`. -/
noncomputable def bMoment {r : ℕ} (X : Model r) (N : ℕ) (b₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (l : List (Fin r × Matrix (Fin 2) (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  condExp N (emb N b₀ * (l.map fun q => X N q.1 * emb N q.2).prod)

/-- The block permutation `σ × id` of the index set `Fin 2 × Fin N`. -/
def blockPerm (σ : Equiv.Perm (Fin 2)) (N : ℕ) : Fin 2 × Fin N ≃ Fin 2 × Fin N :=
  Equiv.prodCongr σ (Equiv.refl _)

/-- Rearrangement of the block structure: conjugate every matrix by the block permutation
matrix of `σ ⊗ 1_N`. -/
def rearrange {r : ℕ} (σ : Equiv.Perm (Fin 2)) (X : Model r) : Model r :=
  fun N i => reindex (blockPerm σ N) (blockPerm σ N) (X N i)

lemma trace_reindex_self {ι : Type*} [Fintype ι] (e : ι ≃ ι) (M : Matrix ι ι ℂ) :
    (reindex e e M).trace = M.trace := by
  simp only [trace, reindex_apply, submatrix_apply, diag_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

lemma eval_reindex {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι)
    (X : Fin r → Matrix ι ι ℂ) (p : FreeAlgebra ℂ (Fin r)) :
    eval (fun i => reindex e e (X i)) p = reindex e e (eval X p) := by
  have h : (reindexAlgEquiv ℂ ℂ e).toAlgHom.comp (eval X) = eval (fun i => reindex e e (X i)) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [eval]
  rw [← h]
  simp

/-- **Rearranging the blocks preserves all joint moments**, for every model, every `N` and every
noncommutative polynomial. -/
theorem rearrange_jointMoment {r : ℕ} (σ : Equiv.Perm (Fin 2)) (X : Model r) (N : ℕ)
    (p : FreeAlgebra ℂ (Fin r)) : jointMoment (rearrange σ X) N p = jointMoment X N p := by
  simp only [jointMoment, ntr]
  rw [show rearrange σ X N = fun i => reindex (blockPerm σ N) (blockPerm σ N) (X N i) from rfl,
    eval_reindex, trace_reindex_self]

/-- The rearrangement acts on block expectations by conjugation by `σ`. -/
theorem rearrange_condExp (σ : Equiv.Perm (Fin 2)) (N : ℕ) (M : BMat N) :
    condExp N (reindex (blockPerm σ N) (blockPerm σ N) M) = reindex σ σ (condExp N M) := by
  ext i j
  simp [condExp, blockPerm]

/-- For every model (in particular for every sample of a random model), the first `B`-valued
moments of the rearranged model are the `σ`-conjugates of those of the original model. -/
theorem rearrange_bMoment_first {r : ℕ} (σ : Equiv.Perm (Fin 2)) (X : Model r) (N : ℕ)
    (i : Fin r) :
    bMoment (rearrange σ X) N 1 [(i, 1)] = reindex σ σ (bMoment X N 1 [(i, 1)]) := by
  have h1 : emb N (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := one_kronecker_one
  simp only [bMoment, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h1,
    one_mul]
  exact rearrange_condExp σ N (X N i)

lemma condExp_emb {N : ℕ} (hN : N ≠ 0) (b : Matrix (Fin 2) (Fin 2) ℂ) : condExp N (emb N b) = b := by
  ext i j
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp [condExp, emb, kroneckerMap_apply, one_apply]
  field_simp

/-- `b ↦ b ⊗ 1_N` as an algebra homomorphism. -/
noncomputable def embHom (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ →ₐ[ℂ] BMat N where
  toFun := emb N
  map_one' := one_kronecker_one
  map_mul' a b := by
    simp only [emb]
    rw [← mul_kronecker_mul, one_mul]
  map_zero' := zero_kronecker _
  map_add' a b := add_kronecker a b _
  commutes' c := by
    simp only [emb, Algebra.algebraMap_eq_smul_one]
    rw [smul_kronecker, one_kronecker_one]

lemma ntr_emb {N : ℕ} (hN : N ≠ 0) (b : Matrix (Fin 2) (Fin 2) ℂ) : ntr (emb N b) = ntr b := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [ntr, emb, trace_kronecker, trace_one, Fintype.card_prod, Fintype.card_fin]
  push_cast
  field_simp

/-! ## The explicit pair of matrix models -/

/-- `A = diag(1,0)`, a self-adjoint projection in `M_2(ℂ)`. -/
def A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- `C = [[0,1],[1,0]]`, a self-adjoint unitary in `M_2(ℂ)`. -/
def C : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The generating pair `(A, C)` in `M_2(ℂ)`. -/
def gen : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![A, C]

/-- First model: `X_N = (A ⊗ 1_N, C ⊗ 1_N)`, two self-adjoint `2N × 2N` matrices. -/
noncomputable def X : Model 2 := fun N i => emb N (gen i)

/-- Second model: the first model with its two diagonal blocks swapped. -/
noncomputable def Y : Model 2 := rearrange (Equiv.swap 0 1) X

theorem X_isHermitian (N : ℕ) (i : Fin 2) : (X N i).IsHermitian := by
  have hA : A.IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A]
  have hC : C.IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [C]
  have key : ∀ b : Matrix (Fin 2) (Fin 2) ℂ, b.IsHermitian → (emb N b).IsHermitian := by
    intro b hb
    simp only [emb, IsHermitian, conjTranspose_kronecker, hb.eq, conjTranspose_one]
  fin_cases i
  · exact key A hA
  · exact key C hC

theorem Y_isHermitian (N : ℕ) (i : Fin 2) : (Y N i).IsHermitian :=
  (X_isHermitian N i).submatrix _

/-- The joint moments of `X` at level `N ≥ 1` are those of `(A, C)` in `(M_2(ℂ), tr_2)`. -/
lemma jointMoment_X {N : ℕ} (hN : N ≠ 0) (p : FreeAlgebra ℂ (Fin 2)) :
    jointMoment X N p = ntr (eval gen p) := by
  have h : (embHom N).comp (eval gen) = eval (X N) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [eval, X]
    rfl
  simp only [jointMoment]
  rw [← h]
  exact ntr_emb hN _

/-- **Main theorem.** The explicit models `X` and `Y = rearrange (swap 0 1) X` satisfy:
1. `Y` is the block rearrangement of `X` (definitionally), and both consist of self-adjoint
   matrices;
2. for every `N` and every noncommutative polynomial `p`, the joint moments agree, and both
   sequences converge to the same limit `tr_2(p(A, C))`;
3. for every `N ≥ 1`, the `M_2(ℂ)`-valued distributions differ, already at the first
   `B`-valued moment `E_N(X_{N,0})`: it is `diag(1,0)` for `X` and `diag(0,1)` for `Y`;
4. hence the limiting `B`-valued first moments differ as well. -/
theorem conjecture4780 :
    Y = rearrange (Equiv.swap 0 1) X ∧
    (∀ N i, (X N i).IsHermitian ∧ (Y N i).IsHermitian) ∧
    (∀ N p, jointMoment X N p = jointMoment Y N p) ∧
    (∀ p, Tendsto (fun N => jointMoment X N p) atTop (𝓝 (ntr (eval gen p))) ∧
          Tendsto (fun N => jointMoment Y N p) atTop (𝓝 (ntr (eval gen p)))) ∧
    (∀ N, N ≠ 0 → bMoment X N 1 [(0, 1)] = !![1, 0; 0, 0] ∧
                  bMoment Y N 1 [(0, 1)] = !![0, 0; 0, 1]) ∧
    (∀ N, N ≠ 0 → bMoment X N 1 [(0, 1)] ≠ bMoment Y N 1 [(0, 1)]) ∧
    (Tendsto (fun N => bMoment X N 1 [(0, 1)]) atTop (𝓝 !![1, 0; 0, 0]) ∧
     Tendsto (fun N => bMoment Y N 1 [(0, 1)]) atTop (𝓝 !![0, 0; 0, 1]) ∧
     (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ≠ !![0, 0; 0, 1]) := by
  have hmom : ∀ N p, jointMoment X N p = jointMoment Y N p := fun N p =>
    (rearrange_jointMoment _ X N p).symm
  have hlimX : ∀ p, Tendsto (fun N => jointMoment X N p) atTop (𝓝 (ntr (eval gen p))) := by
    intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact (jointMoment_X hN p).symm
  have hbX : ∀ N, N ≠ 0 → bMoment X N 1 [(0, 1)] = !![1, 0; 0, 0] := by
    intro N hN
    have : emb N (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := one_kronecker_one
    simp only [bMoment, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      this, one_mul]
    simp only [X, gen, Matrix.cons_val_zero]
    rw [condExp_emb hN]
    rfl
  have hbY : ∀ N, N ≠ 0 → bMoment Y N 1 [(0, 1)] = !![0, 0; 0, 1] := by
    intro N hN
    have : emb N (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := one_kronecker_one
    simp only [bMoment, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      this, one_mul]
    simp only [Y, rearrange]
    rw [rearrange_condExp]
    simp only [X, gen, Matrix.cons_val_zero]
    rw [condExp_emb hN]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A]
  have hne : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ≠ !![0, 0; 0, 1] := by
    intro h
    have := congrFun (congrFun h 0) 0
    simp at this
  refine ⟨rfl, fun N i => ⟨X_isHermitian N i, Y_isHermitian N i⟩, hmom,
    fun p => ⟨hlimX p, ?_⟩, fun N hN => ⟨hbX N hN, hbY N hN⟩, ?_, ?_, ?_, hne⟩
  · exact (hlimX p).congr (fun N => hmom N p)
  · intro N hN
    rw [hbX N hN, hbY N hN]
    exact hne
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact (hbX N hN).symm
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact (hbY N hN).symm

end Conjecture4780
