import Mathlib

/-!
# Conjecture 00000008565: the "abelian simple spectrum law" is false

Clause 2 of the conjecture says that simple spectrum (no multiplicity) is generic for cyclic
generating sets of abelian groups.  We use Mathlib's undirected Cayley graph
`SimpleGraph.addCayley S` (vertices `u ≠ v` adjacent iff `v - u ∈ S` or `u - v ∈ S`) on the
cyclic group `ZMod n` and its adjacency matrix over `ℂ`.

Main results (for every `n ≥ 3` and every `S : Set (ZMod n)`):
* `C8565.exists_eigenspace_finrank_ge_two`: some adjacency eigenspace has dimension `≥ 2`;
* `C8565.exists_charpoly_rootMultiplicity_ge_two`: some eigenvalue is a root of the
  characteristic polynomial of multiplicity `≥ 2`;
* `C8565.not_hasSimpleSpectrum`: the adjacency matrix does not have simple spectrum;
* `C8565.connMatrix_not_hasSimpleSpectrum`: the same for the textbook matrix
  `A(u, v) = [v - u ∈ S]` of a symmetric `S` (loops allowed when `0 ∈ S`);
* `C8565.simple_spectrum_not_generic`: among the generating sets of `ZMod n` (a nonempty
  family), the number with simple spectrum is `0`.

The two eigenvectors are the additive character `χ(x) = exp(2πi x/n)` (`ZMod.stdAddChar`) and
its conjugate `x ↦ χ(-x)`; they share the eigenvalue `∑_{w ~ 0} χ(w)` because the neighbourhood
of `0` is closed under negation, and they are linearly independent because `χ(1) ≠ χ(-1)`.
-/

namespace C8565

open Matrix SimpleGraph

variable {n : ℕ} [NeZero n]

/-- Simple spectrum of a complex square matrix: every eigenspace of the associated linear
operator has dimension at most one. -/
def HasSimpleSpectrum {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Prop :=
  ∀ μ : ℂ, Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' A) μ) ≤ 1

omit [NeZero n] in
/-- Faithfulness check: for a symmetric connection set `S` with `0 ∉ S`, Mathlib's Cayley graph
is the textbook one, `u ~ v ↔ v - u ∈ S`. -/
theorem addCayley_adj_iff_sub_mem (S : Set (ZMod n)) (hsymm : ∀ s ∈ S, -s ∈ S)
    (h0 : (0 : ZMod n) ∉ S) (u v : ZMod n) :
    (addCayley S).Adj u v ↔ v - u ∈ S := by
  rw [addCayley_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · simpa [sub_eq_neg_add] using h
    · simpa [sub_eq_neg_add] using hsymm _ h
  · intro h
    refine ⟨fun huv => h0 (by simpa [huv] using h), Or.inl (by simpa [sub_eq_neg_add] using h)⟩

omit [NeZero n] in
/-- Translation invariance of the Cayley graph. -/
lemma adj_translate (S : Set (ZMod n)) (u w : ZMod n) :
    (addCayley S).Adj u (u + w) ↔ (addCayley S).Adj 0 w := by
  have h := addCayley_adj_add_iff_right (s := S) (d := u) (u := 0) (v := w)
  simpa using h

omit [NeZero n] in
/-- The neighbourhood of `0` is closed under negation. -/
lemma adj_zero_neg (S : Set (ZMod n)) (w : ZMod n) :
    (addCayley S).Adj 0 (-w) ↔ (addCayley S).Adj 0 w := by
  have h := addCayley_adj_add_iff_right (s := S) (d := w) (u := 0) (v := -w)
  simp only [add_zero, add_neg_cancel] at h
  rw [← h, adj_comm]

/-- The eigenvalue attached to `ψ` for the kernel `f`: `∑_w f w * ψ w`. -/
noncomputable def eigval (f ψ : ZMod n → ℂ) : ℂ :=
  ∑ w, f w * ψ w

/-- If `A u v = f (v - u)` (a circulant matrix), every multiplicative function `ψ` (e.g. a
character) is an eigenvector of `A`, with eigenvalue `eigval f ψ`. -/
theorem mulVec_of_mul (A : Matrix (ZMod n) (ZMod n) ℂ) (f : ZMod n → ℂ)
    (hA : ∀ u v, A u v = f (v - u)) (ψ : ZMod n → ℂ) (hψ : ∀ a b, ψ (a + b) = ψ a * ψ b) :
    A *ᵥ ψ = eigval f ψ • ψ := by
  funext u
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, eigval, Finset.sum_mul]
  rw [← Equiv.sum_comp (Equiv.addLeft u)]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Equiv.coe_addLeft, hA, add_sub_cancel_left, hψ u]
  ring

/-- Key lemma.  Let `n ≥ 3` and let `A u v = f (v - u)` with `f` even (`f (-w) = f w`).  Then
`χ` and `x ↦ χ (-x)` are linearly independent eigenvectors of `A` with the same eigenvalue, so
some eigenspace of `A` has dimension at least `2`. -/
theorem exists_eigenspace_finrank_ge_two_of_kernel (hn : 3 ≤ n)
    (A : Matrix (ZMod n) (ZMod n) ℂ) (f : ZMod n → ℂ) (hA : ∀ u v, A u v = f (v - u))
    (hf : ∀ w, f (-w) = f w) :
    ∃ μ : ℂ, 2 ≤ Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' A) μ) := by
  have : Fact (2 < n) := ⟨by omega⟩
  set χ : AddChar (ZMod n) ℂ := ZMod.stdAddChar
  let v₁ : ZMod n → ℂ := fun x => χ x
  let v₂ : ZMod n → ℂ := fun x => χ (-x)
  have h₁ : ∀ a b, v₁ (a + b) = v₁ a * v₁ b := fun a b => AddChar.map_add_eq_mul χ a b
  have h₂ : ∀ a b, v₂ (a + b) = v₂ a * v₂ b := fun a b => by
    simp only [v₂, neg_add, AddChar.map_add_eq_mul]
  have he : eigval f v₂ = eigval f v₁ := by
    unfold eigval
    rw [← Equiv.sum_comp (Equiv.neg (ZMod n))]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [Equiv.neg_apply, hf, v₁, v₂, neg_neg]
  set μ := eigval f v₁
  refine ⟨μ, ?_⟩
  have m₁ : v₁ ∈ Module.End.eigenspace (Matrix.toLin' A) μ := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, mulVec_of_mul A f hA v₁ h₁]
  have m₂ : v₂ ∈ Module.End.eigenspace (Matrix.toLin' A) μ := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, mulVec_of_mul A f hA v₂ h₂, he]
  have hne : χ 1 ≠ χ (-1) := fun h => ZMod.neg_one_ne_one (ZMod.injective_stdAddChar h).symm
  have hli : LinearIndependent ℂ
      ![(⟨v₁, m₁⟩ : Module.End.eigenspace (Matrix.toLin' A) μ), ⟨v₂, m₂⟩] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hv := congrArg Subtype.val hst
    have e0 := congrFun hv 0
    have e1 := congrFun hv 1
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Submodule.coe_zero, Pi.zero_apply, v₁, v₂, neg_zero, AddChar.map_zero_eq_one,
      mul_one] at e0 e1
    have ht : t = -s := by linear_combination e0
    subst ht
    have hs : s * (χ 1 - χ (-1)) = 0 := by linear_combination e1
    have hs0 : s = 0 := (mul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr hne)
    exact ⟨hs0, by simp [hs0]⟩
  simpa using hli.fintype_card_le_finrank

omit [NeZero n] in
/-- The adjacency matrix of `Cay(ZMod n, S)` is circulant: its entry at `(u, v)` depends only
on `v - u`. -/
lemma adjMatrix_eq_kernel (S : Set (ZMod n)) [DecidableRel (addCayley S).Adj] (u v : ZMod n) :
    (addCayley S).adjMatrix ℂ u v = (addCayley S).adjMatrix ℂ 0 (v - u) := by
  have h := adj_translate S u (v - u)
  rw [add_sub_cancel] at h
  simp only [adjMatrix_apply, h]

/-- For `n ≥ 3` and every `S`, some eigenspace of the adjacency operator of the Cayley graph
`Cay(ZMod n, S)` has dimension at least `2`. -/
theorem exists_eigenspace_finrank_ge_two (hn : 3 ≤ n) (S : Set (ZMod n))
    [DecidableRel (addCayley S).Adj] :
    ∃ μ : ℂ, 2 ≤ Module.finrank ℂ
      (Module.End.eigenspace (Matrix.toLin' ((addCayley S).adjMatrix ℂ)) μ) :=
  exists_eigenspace_finrank_ge_two_of_kernel hn _ _ (adjMatrix_eq_kernel S)
    (fun w => by simp only [adjMatrix_apply, adj_zero_neg])

/-- The same eigenvalue is a root of multiplicity at least `2` of the characteristic
polynomial of the adjacency matrix (geometric multiplicity ≤ algebraic multiplicity). -/
theorem exists_charpoly_rootMultiplicity_ge_two (hn : 3 ≤ n) (S : Set (ZMod n))
    [DecidableRel (addCayley S).Adj] :
    ∃ μ : ℂ, 2 ≤ ((addCayley S).adjMatrix ℂ).charpoly.rootMultiplicity μ := by
  obtain ⟨μ, h⟩ := exists_eigenspace_finrank_ge_two hn S
  refine ⟨μ, h.trans ?_⟩
  have := LinearMap.finrank_eigenspace_le (Matrix.toLin' ((addCayley S).adjMatrix ℂ)) μ
  rwa [Matrix.charpoly_toLin'] at this

/-- **Main theorem.** For every `n ≥ 3` and every connection set `S ⊆ ZMod n`, the Cayley graph
`Cay(ZMod n, S)` does not have simple spectrum. -/
theorem not_hasSimpleSpectrum (hn : 3 ≤ n) (S : Set (ZMod n))
    [DecidableRel (addCayley S).Adj] :
    ¬ HasSimpleSpectrum ((addCayley S).adjMatrix ℂ) := by
  intro h
  obtain ⟨μ, hμ⟩ := exists_eigenspace_finrank_ge_two hn S
  have := h μ
  omega

/-- The textbook adjacency matrix of the Cayley graph with symmetric connection set `S`:
`A(u, v) = 1` if `v - u ∈ S` and `0` otherwise (with a loop at every vertex when `0 ∈ S`). -/
def connMatrix (S : Set (ZMod n)) [DecidablePred (· ∈ S)] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun u v => if v - u ∈ S then 1 else 0

/-- The same conclusion for the textbook matrix `A(u, v) = [v - u ∈ S]` of any symmetric `S`
(loops allowed). -/
theorem connMatrix_not_hasSimpleSpectrum (hn : 3 ≤ n) (S : Set (ZMod n)) [DecidablePred (· ∈ S)]
    (hsymm : ∀ s ∈ S, -s ∈ S) : ¬ HasSimpleSpectrum (connMatrix S) := by
  intro h
  have hf : ∀ w : ZMod n, (if -w ∈ S then (1 : ℂ) else 0) = if w ∈ S then 1 else 0 := by
    intro w
    have : -w ∈ S ↔ w ∈ S := ⟨fun hw => by simpa using hsymm _ hw, hsymm w⟩
    simp only [this]
  obtain ⟨μ, hμ⟩ := exists_eigenspace_finrank_ge_two_of_kernel hn (connMatrix S)
    (fun w => if w ∈ S then 1 else 0) (fun u v => rfl) hf
  have := h μ
  omega

/-- `{1}` generates `ZMod n`, so the family of generating sets is nonempty. -/
lemma closure_one_eq_top : AddSubgroup.closure ({1} : Set (ZMod n)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [AddSubgroup.mem_closure_singleton]
  exact ⟨(x.val : ℤ), by simp⟩

open Classical in
/-- **Simple spectrum is not generic.** For every `n ≥ 3`, no generating set `S` of the cyclic
group `ZMod n` gives a Cayley graph with simple spectrum, while generating sets exist; so the
proportion of generating sets with simple spectrum is `0` for every `n ≥ 3`. -/
theorem simple_spectrum_not_generic (hn : 3 ≤ n) :
    (Finset.univ.filter fun S : Finset (ZMod n) =>
        AddSubgroup.closure (S : Set (ZMod n)) = ⊤ ∧
          HasSimpleSpectrum ((addCayley (S : Set (ZMod n))).adjMatrix ℂ)).card = 0 ∧
    0 < (Finset.univ.filter fun S : Finset (ZMod n) =>
        AddSubgroup.closure (S : Set (ZMod n)) = ⊤).card := by
  refine ⟨?_, ?_⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro S - ⟨-, hS⟩
    exact not_hasSimpleSpectrum hn _ hS
  · refine Finset.card_pos.mpr ⟨{1}, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_singleton]
    exact closure_one_eq_top

end C8565
