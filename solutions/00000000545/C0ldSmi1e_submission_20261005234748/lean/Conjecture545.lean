import Connectivity
import IdealBridge
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Sym.Card

noncomputable section

namespace CompleteGraph
open MvPolynomial

variable (V : Type*) [DecidableEq V]
variable (k : Type*) [CommRing k]

/-- The incidence column of an unordered, loopless complete-graph edge. -/
noncomputable def incidence (e : Edge V) : V →₀ ℕ := (ends V e).toFinsupp

/-- The standard edge-ring parametrization, sending edge ij to x_i x_j. -/
def graphRingMap : MvPolynomial (Edge V) k →+* MvPolynomial V k :=
  IdealBridge.toricMap (k := k) (incidence V)

/-- The graph ring is the image of its standard monomial parametrization. -/
def graphRing : Subring (MvPolynomial V k) := (graphRingMap V k).range

/-- The toric ideal of the complete graph's edge ring. -/
def toricIdeal : Ideal (MvPolynomial (Edge V) k) := RingHom.ker (graphRingMap V k)

/-- A multiset of edges is precisely the exponent vector of an edge monomial. -/
def edgeMonomial (M : Multiset (Edge V)) : MvPolynomial (Edge V) k :=
  monomial M.toFinsupp 1

/-- All nonzero quadratic pure binomials in the degree fibers. -/
def quadraticBinomials : Set (MvPolynomial (Edge V) k) :=
  {p | ∃ A B : Multiset (Edge V), A.card = 2 ∧ B.card = 2 ∧
    degree V A = degree V B ∧ A ≠ B ∧ p = edgeMonomial V k A - edgeMonomial V k B}

/-- A finite binomial generating set, every member of which has total degree two. -/
def HasQuadraticMarkovBasis : Prop :=
  ∃ B : Finset (MvPolynomial (Edge V) k),
    Ideal.span (B : Set (MvPolynomial (Edge V) k)) = toricIdeal V k ∧
    ∀ p ∈ B, p.totalDegree = 2 ∧
      ∃ a b : Edge V →₀ ℕ, a ≠ b ∧ a.sum (fun _ n => n) = 2 ∧
        b.sum (fun _ n => n) = 2 ∧ p = monomial a 1 - monomial b 1

variable {V k}

@[simp] theorem incidence_edge (a b : V) (h : a ≠ b) :
    incidence V (edge V a b h) = Finsupp.single a 1 + Finsupp.single b 1 := by
  simp [incidence, ← Multiset.singleton_add, Multiset.toFinsupp_add]

@[simp] theorem graphRingMap_edge (a b : V) (h : a ≠ b) :
    graphRingMap V k (X (edge V a b h)) = X a * X b := by
  simp [graphRingMap, X, monomial_mul]

theorem exponentMap_toFinsupp (M : Multiset (Edge V)) :
    IdealBridge.exponentMap (incidence V) M.toFinsupp = (degree V M).toFinsupp := by
  induction M using Multiset.induction_on with
  | empty => simp [Multiset.toFinsupp_zero]
  | @cons e M ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, map_add]
    simp [ih, incidence, degree, Multiset.toFinsupp_add]

@[simp] theorem graphRingMap_edgeMonomial (M : Multiset (Edge V)) :
    graphRingMap V k (edgeMonomial V k M) = monomial (degree V M).toFinsupp 1 := by
  simp [graphRingMap, edgeMonomial, exponentMap_toFinsupp]

@[simp] theorem edgeMonomial_add (M N : Multiset (Edge V)) :
    edgeMonomial V k (M + N) = edgeMonomial V k M * edgeMonomial V k N := by
  simp [edgeMonomial, Multiset.toFinsupp_add, monomial_mul]

theorem SwitchEquiv.binomial_mem {M N : Multiset (Edge V)} (h : SwitchEquiv M N) :
    edgeMonomial V k M - edgeMonomial V k N ∈ Ideal.span (quadraticBinomials V k) := by
  induction h with
  | refl => simp
  | @trans M N P _ _ ih₁ ih₂ =>
    convert (Ideal.span (quadraticBinomials V k)).add_mem ih₁ ih₂ using 1
    ring
  | @add M N R _ ih =>
    rw [edgeMonomial_add, edgeMonomial_add, ← sub_mul]
    exact (Ideal.span (quadraticBinomials V k)).mul_mem_right _ ih
  | quad A B hA hB hdeg =>
    by_cases hAB : A = B
    · simp [hAB]
    · exact Ideal.subset_span ⟨A,B,hA,hB,hdeg,hAB,rfl⟩

/-- No degree truncation: these quadrics generate the entire toric ideal. -/
theorem toricIdeal_eq_span_quadraticBinomials :
    toricIdeal V k = Ideal.span (quadraticBinomials V k) := by
  apply le_antisymm
  · apply IdealBridge.ker_le_of_fiber_binomials
    intro a b hab
    have hdeg : degree V a.toMultiset = degree V b.toMultiset := by
      apply Multiset.toFinsupp.injective
      rw [← exponentMap_toFinsupp, ← exponentMap_toFinsupp]
      simpa using hab
    have hh := (connected_of_degree_eq a.toMultiset b.toMultiset hdeg).binomial_mem (k := k)
    simpa [edgeMonomial] using hh
  · apply Ideal.span_le.mpr
    rintro p ⟨A,B,_hA,_hB,hdeg,_hAB,rfl⟩
    change graphRingMap V k (edgeMonomial V k A - edgeMonomial V k B) = 0
    simp [hdeg]

theorem quadraticBinomials_finite [Fintype V] : (quadraticBinomials V k).Finite := by
  let f : Sym (Edge V) 2 × Sym (Edge V) 2 → MvPolynomial (Edge V) k := fun x =>
    edgeMonomial V k x.1.val - edgeMonomial V k x.2.val
  apply (Set.finite_range f).subset
  rintro p ⟨A,B,hA,hB,_hdeg,_hAB,rfl⟩
  exact ⟨(⟨A,hA⟩,⟨B,hB⟩),rfl⟩

variable [Nontrivial k]

theorem edgeMonomial_injective : Function.Injective (edgeMonomial V k) :=
  (MvPolynomial.monomial_left_injective (one_ne_zero : (1 : k) ≠ 0)).comp
    Multiset.toFinsupp.injective

theorem quadraticBinomials_totalDegree {p : MvPolynomial (Edge V) k}
    (hp : p ∈ quadraticBinomials V k) : p.totalDegree = 2 := by
  obtain ⟨A,B,hA,hB,_hdeg,hAB,rfl⟩ := hp
  have hn : edgeMonomial V k A - edgeMonomial V k B ≠ 0 := by
    intro h
    exact hAB (edgeMonomial_injective (sub_eq_zero.mp h))
  apply MvPolynomial.IsHomogeneous.totalDegree _ hn
  apply MvPolynomial.IsHomogeneous.sub
  · apply MvPolynomial.isHomogeneous_monomial
    simpa [Finsupp.degree, Finsupp.sum] using hA
  · apply MvPolynomial.isHomogeneous_monomial
    simpa [Finsupp.degree, Finsupp.sum] using hB

/-- Every finite complete graph admits a finite entirely quadratic Markov basis. -/
theorem hasQuadraticMarkovBasis [Fintype V] : HasQuadraticMarkovBasis V k := by
  let B := (quadraticBinomials_finite (V := V) (k := k)).toFinset
  refine ⟨B, ?_, ?_⟩
  · simpa [B] using (toricIdeal_eq_span_quadraticBinomials (V := V) (k := k)).symm
  · intro p hp
    have hq : p ∈ quadraticBinomials V k := by simpa [B] using hp
    refine ⟨quadraticBinomials_totalDegree hq, ?_⟩
    obtain ⟨A,C,hA,hC,_hdeg,hAC,rfl⟩ := hq
    refine ⟨A.toFinsupp,C.toFinsupp,fun h => hAC (Multiset.toFinsupp.injective h),?_,?_,rfl⟩
    · simpa only [← hA] using Multiset.toFinsupp_sum_eq A
    · simpa only [← hC] using Multiset.toFinsupp_sum_eq C

/-- The source's claimed cutoff already fails at n = 6. -/
theorem counterexample_six : HasQuadraticMarkovBasis (Fin 6) k ∧ ¬ (6 ≤ 5) := by
  exact ⟨hasQuadraticMarkovBasis, by omega⟩

/-- Negation of the original universal if-and-only-if statement. -/
theorem conjecture545_false :
    ¬ (∀ n : ℕ, HasQuadraticMarkovBasis (Fin n) k ↔ n ≤ 5) := by
  intro h
  exact (counterexample_six (k := k)).2 ((h 6).mp (counterexample_six (k := k)).1)

/-- The same contradiction with the usual positive-integer domain for K_n. -/
theorem conjecture545_false_positive :
    ¬ (∀ n : ℕ, 0 < n → (HasQuadraticMarkovBasis (Fin n) k ↔ n ≤ 5)) := by
  intro h
  exact (counterexample_six (k := k)).2 ((h 6 (by omega)).mp
    (counterexample_six (k := k)).1)

end CompleteGraph
