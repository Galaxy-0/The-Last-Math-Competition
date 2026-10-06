import Conjecture545

open CompleteGraph

example (k : Type*) [Field k] : HasQuadraticMarkovBasis (Fin 6) k :=
  hasQuadraticMarkovBasis

example (k : Type*) [Field k] :
    ¬ (∀ n : ℕ, HasQuadraticMarkovBasis (Fin n) k ↔ n ≤ 5) :=
  conjecture545_false

example (k : Type*) [Field k] :
    ¬ (∀ n : ℕ, 0 < n → (HasQuadraticMarkovBasis (Fin n) k ↔ n ≤ 5)) :=
  conjecture545_false_positive

example (k : Type*) [Field k] (i j : Fin 6) (h : i ≠ j) :
    graphRingMap (Fin 6) k (MvPolynomial.X (edge (Fin 6) i j h)) =
      MvPolynomial.X i * MvPolynomial.X j :=
  graphRingMap_edge i j h

example (k : Type*) [Field k] :
    toricIdeal (Fin 6) k = Ideal.span (quadraticBinomials (Fin 6) k) :=
  toricIdeal_eq_span_quadraticBinomials
