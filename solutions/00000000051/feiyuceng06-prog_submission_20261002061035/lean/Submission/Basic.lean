import Mathlib

/-!
# Conjecture 00000000051 holds

Conjecture 00000000051 asserts that there are infinitely many pairwise
non-isomorphic connected integral graphs whose adjacency spectrum consists only
of `0` and numbers `±p` with `p` prime.

The complete bipartite graphs `K_{p,p}`, `p` prime, are such a family. Their
adjacency matrix `A` satisfies `A³ = p² A`: the number of walks of length `2`
between two vertices is `p` if they lie on the same side and `0` otherwise. So
every eigenvalue `μ` satisfies `μ³ = p² μ`, i.e. `μ ∈ {0, p, -p}`, which are
integers. `K_{p,p}` is connected, and graphs `K_{p,p}` for different primes have
different numbers of vertices, hence are not isomorphic.

The adjacency spectrum of a finite graph is taken over `ℂ`, as the spectrum of
its adjacency matrix in the matrix algebra (`spectrum ℂ (G.adjMatrix ℂ)`), which
is exactly its set of complex eigenvalues.
-/

namespace Submission00000000051

open Matrix Polynomial

section Definitions

variable {V : Type} [Fintype V]

open scoped Classical in
/-- The adjacency spectrum of a finite simple graph: the set of complex
eigenvalues of its adjacency matrix. -/
noncomputable def adjSpectrum (G : SimpleGraph V) : Set ℂ :=
  spectrum ℂ (G.adjMatrix ℂ)

/-- An *integral graph*: every adjacency eigenvalue is an integer. -/
def IsIntegralGraph (G : SimpleGraph V) : Prop :=
  ∀ μ ∈ adjSpectrum G, ∃ z : ℤ, μ = z

/-- The adjacency spectrum consists only of `0` and numbers `±p`, `p` prime. -/
def SpectrumZeroOrPmPrime (G : SimpleGraph V) : Prop :=
  ∀ μ ∈ adjSpectrum G, μ = 0 ∨ ∃ p : ℕ, p.Prime ∧ (μ = p ∨ μ = -p)

/-- The graphs the conjecture is about: connected, integral, with adjacency
spectrum inside `{0} ∪ {±p : p prime}`. -/
def IsGood (G : SimpleGraph V) : Prop :=
  G.Connected ∧ IsIntegralGraph G ∧ SpectrumZeroOrPmPrime G

end Definitions

/-- Conjecture 00000000051: there are infinitely many pairwise non-isomorphic
finite graphs with the property `IsGood`, i.e. an infinite sequence of them, no
two of which are isomorphic. -/
def ConjectureHolds : Prop :=
  ∃ (V : ℕ → Type) (_ : ∀ k, Fintype (V k)) (G : ∀ k, SimpleGraph (V k)),
    (∀ k, IsGood (G k)) ∧ ∀ j k, j ≠ k → IsEmpty (G j ≃g G k)

/-- If `A³ = c² A`, every eigenvalue of `A` is `0`, `c` or `-c`. -/
theorem spectrum_subset_of_cube {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (c : ℂ) (h : A ^ 3 = c ^ 2 • A) :
    ∀ μ ∈ spectrum ℂ A, μ = 0 ∨ μ = c ∨ μ = -c := by
  intro μ hμ
  have hmem := spectrum.subset_polynomial_aeval A (X ^ 3 - C (c ^ 2) * X) ⟨μ, hμ, rfl⟩
  have haeval : aeval A (X ^ 3 - C (c ^ 2) * X : ℂ[X]) = 0 := by
    simp [h, Algebra.smul_def]
  have hval : eval μ (X ^ 3 - C (c ^ 2) * X) = μ ^ 3 - c ^ 2 * μ := by simp
  beta_reduce at hmem
  rw [haeval, hval] at hmem
  -- The only point of the spectrum of `0` is `0`: a nonzero scalar is a unit.
  have hzero : μ ^ 3 - c ^ 2 * μ = 0 := by
    by_contra hne
    apply spectrum.mem_iff.mp hmem
    rw [sub_zero]
    exact (isUnit_iff_ne_zero.mpr hne).map (algebraMap ℂ (Matrix n n ℂ))
  have hfac : μ * (μ - c) * (μ + c) = 0 := by linear_combination hzero
  rcases mul_eq_zero.mp hfac with h₁ | h₁
  · rcases mul_eq_zero.mp h₁ with h₂ | h₂
    · exact Or.inl h₂
    · exact Or.inr (Or.inl (sub_eq_zero.mp h₂))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h₁))

/-- `K_{m,m}` on `Fin m ⊕ Fin m`. -/
abbrev K (m : ℕ) : SimpleGraph (Fin m ⊕ Fin m) := completeBipartiteGraph (Fin m) (Fin m)

theorem K_adj_inl_inl (m : ℕ) (a b : Fin m) : ¬ (K m).Adj (.inl a) (.inl b) := by
  simp [K]

theorem K_adj_inr_inr (m : ℕ) (a b : Fin m) : ¬ (K m).Adj (.inr a) (.inr b) := by
  simp [K]

theorem K_adj_inl_inr (m : ℕ) (a b : Fin m) : (K m).Adj (.inl a) (.inr b) := by
  simp [K]

theorem K_adj_inr_inl (m : ℕ) (a b : Fin m) : (K m).Adj (.inr a) (.inl b) := by
  simp [K]

section Spectrum

variable (m : ℕ) [DecidableRel (K m).Adj]

/-- Walks of length two in `K_{m,m}`: `m` between vertices on the same side,
none between vertices on opposite sides. -/
theorem adjMatrix_sq_apply (i j : Fin m ⊕ Fin m) :
    ((K m).adjMatrix ℂ * (K m).adjMatrix ℂ) i j =
      if i.isLeft = j.isLeft then (m : ℂ) else 0 := by
  rw [mul_apply, Fintype.sum_sum_type]
  rcases i with a | a <;> rcases j with b | b <;>
    simp [SimpleGraph.adjMatrix_apply]

/-- The adjacency matrix of `K_{m,m}` satisfies `A³ = m² A`. -/
theorem adjMatrix_cube : (K m).adjMatrix ℂ ^ 3 = (m : ℂ) ^ 2 • (K m).adjMatrix ℂ := by
  ext i j
  rw [pow_three, mul_apply, Fintype.sum_sum_type]
  simp_rw [adjMatrix_sq_apply]
  rcases i with a | a <;> rcases j with b | b <;>
    simp [SimpleGraph.adjMatrix_apply] <;>
    ring

end Spectrum

/-- For a prime `p`, every adjacency eigenvalue of `K_{p,p}` is `0`, `p` or `-p`. -/
theorem adjSpectrum_K {p : ℕ} (μ : ℂ) (hμ : μ ∈ adjSpectrum (K p)) :
    μ = 0 ∨ μ = p ∨ μ = -p := by
  classical
  unfold adjSpectrum at hμ
  convert spectrum_subset_of_cube _ (p : ℂ) (adjMatrix_cube p) μ (by convert hμ)

theorem K_connected {m : ℕ} (hm : 0 < m) : (K m).Connected := by
  have hreach : ∀ u v : Fin m ⊕ Fin m, (K m).Reachable u v := by
    have h0 : ∀ a b : Fin m, (K m).Reachable (.inl a) (.inr b) :=
      fun a b => (K_adj_inl_inr m a b).reachable
    rintro (a | a) (b | b)
    · exact (h0 a ⟨0, hm⟩).trans (h0 b ⟨0, hm⟩).symm
    · exact h0 a b
    · exact (h0 b a).symm
    · exact (h0 ⟨0, hm⟩ a).symm.trans (h0 ⟨0, hm⟩ b)
  have : Nonempty (Fin m ⊕ Fin m) := ⟨.inl ⟨0, hm⟩⟩
  exact ⟨hreach⟩

/-- `K_{p,p}` has all the properties required by the conjecture. -/
theorem isGood_K {p : ℕ} (hp : p.Prime) : IsGood (K p) := by
  refine ⟨K_connected hp.pos, ?_, ?_⟩
  · intro μ hμ
    rcases adjSpectrum_K μ hμ with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨p, by simp⟩
    · exact ⟨-p, by simp⟩
  · intro μ hμ
    rcases adjSpectrum_K μ hμ with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨p, hp, Or.inl rfl⟩
    · exact Or.inr ⟨p, hp, Or.inr rfl⟩

/-- Conjecture 00000000051 holds: the graphs `K_{p,p}` over the primes
`p = 2, 3, 5, 7, …` form an infinite family of pairwise non-isomorphic connected
integral graphs with adjacency spectrum `{0, p, -p}`. -/
theorem conjecture_00000000051 : ConjectureHolds := by
  refine ⟨fun k => Fin (Nat.nth Nat.Prime k) ⊕ Fin (Nat.nth Nat.Prime k),
    fun _ => inferInstance, fun k => K (Nat.nth Nat.Prime k),
    fun k => isGood_K (Nat.prime_nth_prime k), ?_⟩
  intro j k hjk
  refine ⟨fun e => hjk (Nat.nth_injective Nat.infinite_setOfPred_prime ?_)⟩
  have hcard := Fintype.card_congr e.toEquiv
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  show Nat.nth Nat.Prime j = Nat.nth Nat.Prime k
  omega

end Submission00000000051

#print axioms Submission00000000051.conjecture_00000000051
