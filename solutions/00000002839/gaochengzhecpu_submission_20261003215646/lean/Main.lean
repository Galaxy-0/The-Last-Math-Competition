import Std

namespace Conjecture2839
universe u

/-- An integral domain, presented by its ordinary ring operations and laws.
The two redundant last laws expose exactly the cancellation facts used below.
All these hypotheses hold over every field, including C. -/
structure DomainData (K : Type u) where
  zero : K
  one : K
  add : K → K → K
  mul : K → K → K
  neg : K → K
  sub : K → K → K
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  zero_mul : ∀ a, mul zero a = zero
  mul_zero : ∀ a, mul a zero = zero
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  one_ne_zero : one ≠ zero
  sub_def : ∀ a b, sub a b = add a (neg b)
  sub_zero_iff : ∀ a b, sub a b = zero ↔ a = b
  product_zero_iff : ∀ a b, mul a b = zero ↔ a = zero ∨ b = zero

abbrev PointSet (K : Type u) := K → Prop

/-- Ordinary univariate polynomial expressions. No inverse or arbitrary
function constructor occurs. Coefficient-list polynomials embed by Horner. -/
inductive Polynomial (K : Type u) where
  | constant : K → Polynomial K
  | X : Polynomial K
  | add : Polynomial K → Polynomial K → Polynomial K
  | mul : Polynomial K → Polynomial K → Polynomial K
  | neg : Polynomial K → Polynomial K

def evaluate {K : Type u} (D : DomainData K) (x : K) : Polynomial K → K
  | .constant a => a
  | .X => x
  | .add p q => D.add (evaluate D x p) (evaluate D x q)
  | .mul p q => D.mul (evaluate D x p) (evaluate D x q)
  | .neg p => D.neg (evaluate D x p)

def ofCoefficients {K : Type u} (D : DomainData K) : List K → Polynomial K
  | [] => .constant D.zero
  | a :: as => .add (.constant a) (.mul .X (ofCoefficients D as))

def horner {K : Type u} (D : DomainData K) (x : K) : List K → K
  | [] => D.zero
  | a :: as => D.add a (D.mul x (horner D x as))

theorem coefficient_bridge {K : Type u} (D : DomainData K) (x : K) (as : List K) :
    evaluate D x (ofCoefficients D as) = horner D x as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [ofCoefficients, evaluate, horner, ih]

def ZariskiClosed {K : Type u} (D : DomainData K) (S : PointSet K) : Prop :=
  ∃ equations : Polynomial K → Prop,
    ∀ x, S x ↔ ∀ p, equations p → evaluate D x p = D.zero

/-- The vanishing-ideal definition V(I(S)) of the Zariski closure. -/
def closure {K : Type u} (D : DomainData K) (S : PointSet K) : PointSet K :=
  fun x => ∀ p : Polynomial K, (∀ y, S y → evaluate D y p = D.zero) → evaluate D x p = D.zero

theorem subset_closure {K : Type u} (D : DomainData K) (S : PointSet K) :
    ∀ x, S x → closure D S x := by
  intro x hx p hp
  exact hp x hx

theorem closure_is_closed {K : Type u} (D : DomainData K) (S : PointSet K) :
    ZariskiClosed D (closure D S) := by
  exact ⟨(fun p => ∀ y, S y → evaluate D y p = D.zero), fun _ => Iff.rfl⟩

theorem closure_minimal {K : Type u} (D : DomainData K) (S T : PointSet K)
    (hc : ZariskiClosed D T) (hsub : ∀ x, S x → T x) :
    ∀ x, closure D S x → T x := by
  obtain ⟨equations,heq⟩ := hc
  intro x hx
  apply (heq x).mpr
  intro p hp
  apply hx p
  intro y hy
  exact (heq y).mp (hsub y hy) p hp

def singleton {K : Type u} (a : K) : PointSet K := fun x => x = a
def pair {K : Type u} (a b : K) : PointSet K := fun x => x = a ∨ x = b

def linearFactor {K : Type u} (_D : DomainData K) (a : K) : Polynomial K :=
  .add .X (.neg (.constant a))

theorem linear_zero_iff {K : Type u} (D : DomainData K) (a x : K) :
    evaluate D x (linearFactor D a) = D.zero ↔ x = a := by
  change D.add x (D.neg a) = D.zero ↔ x = a
  rw [← D.sub_def]
  exact D.sub_zero_iff x a

theorem quadratic_zero_iff {K : Type u} (D : DomainData K) (a b x : K) :
    evaluate D x (.mul (linearFactor D a) (linearFactor D b)) = D.zero ↔ pair a b x := by
  change D.mul _ _ = D.zero ↔ _
  rw [D.product_zero_iff, linear_zero_iff, linear_zero_iff]
  rfl

theorem singleton_closed {K : Type u} (D : DomainData K) (a : K) :
    ZariskiClosed D (singleton a) := by
  refine ⟨(fun p => p = linearFactor D a), ?_⟩
  intro x
  constructor
  · intro hx p hp
    subst p
    exact (linear_zero_iff D a x).mpr hx
  · intro h
    exact (linear_zero_iff D a x).mp (h _ rfl)

theorem pair_closed {K : Type u} (D : DomainData K) (a b : K) :
    ZariskiClosed D (pair a b) := by
  refine ⟨(fun p => p = .mul (linearFactor D a) (linearFactor D b)), ?_⟩
  intro x
  constructor
  · intro hx p hp
    subst p
    exact (quadratic_zero_iff D a b x).mpr hx
  · intro h
    exact (quadratic_zero_iff D a b x).mp (h _ rfl)

theorem pair_closure_exact {K : Type u} (D : DomainData K) (a b : K) :
    closure D (pair a b) = pair a b := by
  funext x
  exact propext ⟨closure_minimal D _ _ (pair_closed D a b) (fun _ h => h) x,
    subset_closure D _ x⟩

def Subset {K : Type u} (S T : PointSet K) : Prop := ∀ x, S x → T x
def ProperSubset {K : Type u} (S T : PointSet K) : Prop :=
  Subset S T ∧ ∃ x, T x ∧ ¬S x

/-- Nonempty irreducible closed subsets, using arbitrary closed covers. -/
def IrreducibleClosedIn {K : Type u} (D : DomainData K) (ambient S : PointSet K) : Prop :=
  (∃ x, S x) ∧ Subset S ambient ∧ ZariskiClosed D S ∧
  ∀ A B : PointSet K, ZariskiClosed D A → ZariskiClosed D B →
    (∀ x, S x → A x ∨ B x) → Subset S A ∨ Subset S B

theorem singleton_irreducible {K : Type u} (D : DomainData K) (T : PointSet K)
    (a : K) (ha : T a) : IrreducibleClosedIn D T (singleton a) := by
  refine ⟨⟨a,rfl⟩, ?_, singleton_closed D a, ?_⟩
  · intro x hx
    change x = a at hx
    simpa only [hx] using ha
  · intro A B _ _ hcover
    rcases hcover a rfl with hA | hB
    · exact Or.inl (fun x hx => by change x = a at hx; simpa only [hx] using hA)
    · exact Or.inr (fun x hx => by change x = a at hx; simpa only [hx] using hB)

theorem nonempty_subset_singleton_eq {K : Type u} (S : PointSet K) (a : K)
    (hn : ∃ x, S x) (hs : Subset S (singleton a)) : S = singleton a := by
  obtain ⟨x,hx⟩ := hn
  have hxa := hs x hx
  change x = a at hxa
  have ha : S a := by simpa only [hxa] using hx
  funext y
  apply propext
  constructor
  · exact hs y
  · intro hy
    change y = a at hy
    simpa only [hy] using ha

theorem irreducibles_of_pair {K : Type u} (D : DomainData K) (a b : K) (S : PointSet K)
    (h : IrreducibleClosedIn D (pair a b) S) : S = singleton a ∨ S = singleton b := by
  have hcover := h.2.2.2 (singleton a) (singleton b) (singleton_closed D a)
    (singleton_closed D b) (fun x hx => h.2.1 x hx)
  rcases hcover with ha | hb
  · exact Or.inl (nonempty_subset_singleton_eq S a h.1 ha)
  · exact Or.inr (nonempty_subset_singleton_eq S b h.1 hb)

theorem singleton_not_proper {K : Type u} (a b : K) :
    ¬ProperSubset (singleton a) (singleton b) := by
  rintro ⟨hsub,x,hx,hn⟩
  have hab := hsub a rfl
  change a = b at hab
  change x = b at hx
  exact hn (hx.trans hab.symm)

/-- Standard Krull/topological dimension: a length-n strict chain of
nonempty irreducible closed subsets witnesses dimension at least n. -/
def DimensionAtLeast {K : Type u} (D : DomainData K) (T : PointSet K) (n : Nat) : Prop :=
  ∃ C : Fin (n+1) → PointSet K,
    (∀ i, IrreducibleClosedIn D T (C i)) ∧
    ∀ i : Fin n, ProperSubset (C i.castSucc) (C i.succ)

theorem pair_dimension_at_least_zero {K : Type u} (D : DomainData K) (a b : K) :
    DimensionAtLeast D (pair a b) 0 := by
  refine ⟨(fun _ => singleton a), ?_, ?_⟩
  · intro i
    exact singleton_irreducible D _ a (Or.inl rfl)
  · intro i
    exact Fin.elim0 i

theorem pair_dimension_not_one {K : Type u} (D : DomainData K) (a b : K) :
    ¬DimensionAtLeast D (pair a b) 1 := by
  rintro ⟨C,hC,hstrict⟩
  have h0 := irreducibles_of_pair D a b (C 0) (hC 0)
  have h1 := irreducibles_of_pair D a b (C 1) (hC 1)
  have hp : ProperSubset (C 0) (C 1) := hstrict 0
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rw [h0,h1] at hp <;> exact singleton_not_proper _ _ hp

theorem every_two_point_closure_dimension_zero {K : Type u} (D : DomainData K) (a b : K) :
    DimensionAtLeast D (closure D (pair a b)) 0 ∧
    ¬DimensionAtLeast D (closure D (pair a b)) 1 := by
  rw [pair_closure_exact]
  exact ⟨pair_dimension_at_least_zero D a b, pair_dimension_not_one D a b⟩

/-- This rules out every distinct two-point sample, hence also every generic
one. At n=2 and ambient affine dimension d=1, the claimed min(n-1,d) is 1. -/
theorem conjecture2839_false {K : Type u} (D : DomainData K) :
    ¬∃ a b : K, a ≠ b ∧ DimensionAtLeast D (closure D (pair a b)) (min (2-1) 1) := by
  rintro ⟨a,b,_,h⟩
  exact (every_two_point_closure_dimension_zero D a b).2 h

/-- Concrete consistency check; the preceding proof is universal over all
integral domains and therefore is not limited to this integer model. -/
def integerDomain : DomainData Int where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  sub := (· - ·)
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_neg := Int.add_right_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  one_ne_zero := by decide
  sub_def := fun _ _ => Int.sub_eq_add_neg
  sub_zero_iff := fun _ _ => Int.sub_eq_zero
  product_zero_iff := fun _ _ => Int.mul_eq_zero

#print axioms coefficient_bridge
#print axioms closure_minimal
#print axioms pair_closure_exact
#print axioms irreducibles_of_pair
#print axioms every_two_point_closure_dimension_zero
#print axioms conjecture2839_false
#print axioms integerDomain
end Conjecture2839
