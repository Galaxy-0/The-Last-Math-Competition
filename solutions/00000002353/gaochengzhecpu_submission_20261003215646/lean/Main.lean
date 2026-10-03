import Std

namespace Conjecture2353
universe u

/-- Ordinary commutative-field laws, plus the element 1/2. The final theorem
is universal in this structure, so in particular applies over R and C. -/
structure FieldData (K : Type u) where
  zero : K
  one : K
  half : K
  add : K → K → K
  mul : K → K → K
  neg : K → K
  inv : K → K
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  neg_add : ∀ a, add (neg a) a = zero
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
  inverse : ∀ a, a ≠ zero → mul a (inv a) = one
  half_spec : mul (add one one) half = one

abbrev Matrix (K : Type u) (n : Nat) := Fin n → Fin n → K

def identity {K : Type u} (F : FieldData K) (n : Nat) : Matrix K n :=
  fun i j => if i = j then F.one else F.zero
def multiply {K : Type u} (F : FieldData K) {n : Nat}
    (A B : Matrix K n) : Matrix K n :=
  fun i j => ((List.finRange n).map (fun k => F.mul (A i k) (B k j))).foldr F.add F.zero
def midpoint {K : Type u} (F : FieldData K) {n : Nat}
    (A B : Matrix K n) : Matrix K n := fun i j => F.mul (F.add (A i j) (B i j)) F.half

def IsInverse {K : Type u} (F : FieldData K) {n : Nat}
    (A B : Matrix K n) : Prop :=
  multiply F A B = identity F n ∧ multiply F B A = identity F n

inductive Expression where
  | variable
  | inverse : Expression → Expression

/-- Matrix well-definedness of the rational expression, with genuine matrix
multiplication and two-sided inversion. This fragment contains x^{-1}. -/
def Evaluates {K : Type u} (F : FieldData K) {n : Nat}
    (X : Matrix K n) : Expression → Matrix K n → Prop
  | .variable, Y => Y = X
  | .inverse e, Y => ∃ Z, Evaluates F X e Z ∧ IsInverse F Z Y

def Domain {K : Type u} (F : FieldData K) (e : Expression)
    {n : Nat} (X : Matrix K n) : Prop := ∃ Y, Evaluates F X e Y

def reciprocal : Expression := .inverse .variable

theorem reciprocal_domain {K : Type u} (F : FieldData K) {n : Nat} (X : Matrix K n) :
    Domain F reciprocal X ↔ ∃ Y, IsInverse F X Y := by
  constructor
  · rintro ⟨Y,Z,hZ,hInv⟩
    change Z = X at hZ
    subst Z
    exact ⟨Y,hInv⟩
  · rintro ⟨Y,hY⟩
    exact ⟨Y,X,rfl,hY⟩

def scalarMatrix {K : Type u} (x : K) : Matrix K 1 := fun _ _ => x

theorem scalar_matrix_product {K : Type u} (F : FieldData K) (a b : K) :
    multiply F (scalarMatrix a) (scalarMatrix b) = scalarMatrix (F.mul a b) := by
  funext i j
  simp [multiply, scalarMatrix, List.finRange_succ, List.finRange_zero, F.add_zero]

theorem scalar_identity {K : Type u} (F : FieldData K) :
    identity F 1 = scalarMatrix F.one := by
  funext i j
  have hi : i = 0 := by have := i.isLt; omega
  have hj : j = 0 := by have := j.isLt; omega
  subst i; subst j
  rfl

theorem scalar_inverse_bridge {K : Type u} (F : FieldData K) (a b : K) :
    IsInverse F (scalarMatrix a) (scalarMatrix b) ↔
      F.mul a b = F.one ∧ F.mul b a = F.one := by
  unfold IsInverse
  rw [scalar_matrix_product, scalar_matrix_product, scalar_identity]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨congrFun (congrFun h1 0) 0, congrFun (congrFun h2 0) 0⟩
  · rintro ⟨h1,h2⟩
    exact ⟨by rw [h1], by rw [h2]⟩

theorem neg_one_nonzero {K : Type u} (F : FieldData K) : F.neg F.one ≠ F.zero := by
  intro h
  have hz := F.add_neg F.one
  rw [h,F.add_zero] at hz
  exact F.one_ne_zero hz

theorem positive_in_domain {K : Type u} (F : FieldData K) :
    Domain F reciprocal (scalarMatrix F.one) := by
  apply (reciprocal_domain F _).mpr
  refine ⟨scalarMatrix F.one, (scalar_inverse_bridge F _ _).mpr ?_⟩
  exact ⟨F.one_mul _, F.one_mul _⟩

theorem negative_in_domain {K : Type u} (F : FieldData K) :
    Domain F reciprocal (scalarMatrix (F.neg F.one)) := by
  apply (reciprocal_domain F _).mpr
  refine ⟨scalarMatrix (F.inv (F.neg F.one)), (scalar_inverse_bridge F _ _).mpr ?_⟩
  have hi := F.inverse (F.neg F.one) (neg_one_nonzero F)
  exact ⟨hi, (F.mul_comm _ _).trans hi⟩

theorem zero_not_in_domain {K : Type u} (F : FieldData K) :
    ¬Domain F reciprocal (scalarMatrix F.zero) := by
  intro h
  obtain ⟨Y,hY⟩ := (reciprocal_domain F _).mp h
  have he := congrFun (congrFun hY.1 0) 0
  have hzero : multiply F (scalarMatrix F.zero) Y 0 0 = F.zero := by
    simp [multiply, scalarMatrix, List.finRange_succ, List.finRange_zero,
      F.zero_mul, F.add_zero]
  rw [hzero] at he
  change F.zero = F.one at he
  exact F.one_ne_zero he.symm

theorem midpoint_is_zero {K : Type u} (F : FieldData K) :
    midpoint F (scalarMatrix F.one) (scalarMatrix (F.neg F.one)) =
      scalarMatrix F.zero := by
  funext i j
  exact (congrArg (fun t => F.mul t F.half) (F.add_neg F.one)).trans (F.zero_mul F.half)

/-- Closure under same-size midpoints is necessary for matrix convexity;
the usual matrix-convex combination uses V1=V2=I/sqrt(2). -/
def MidpointClosedAtEveryLevel {K : Type u} (F : FieldData K) (e : Expression) : Prop :=
  ∀ n, ∀ A B : Matrix K n, Domain F e A → Domain F e B → Domain F e (midpoint F A B)

theorem conjecture2353_false {K : Type u} (F : FieldData K) :
    ¬MidpointClosedAtEveryLevel F reciprocal := by
  intro h
  have hz := h 1 (scalarMatrix F.one) (scalarMatrix (F.neg F.one))
    (positive_in_domain F) (negative_in_domain F)
  rw [midpoint_is_zero] at hz
  exact zero_not_in_domain F hz

/-- A concrete field model checks consistency of the universally quantified
field interface. The theorem itself applies to every characteristic-not-two
field, including the intended real and complex scalar fields. -/
def fieldThree : FieldData (Fin 3) where
  zero := 0
  one := 1
  half := 2
  add a b := ⟨(a.val+b.val)%3, Nat.mod_lt _ (by decide)⟩
  mul a b := ⟨(a.val*b.val)%3, Nat.mod_lt _ (by decide)⟩
  neg a := ⟨(3-a.val)%3, Nat.mod_lt _ (by decide)⟩
  inv a := a
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  add_zero := by decide
  neg_add := by decide
  add_neg := by decide
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  one_ne_zero := by decide
  inverse := by decide
  half_spec := by decide

#print axioms reciprocal_domain
#print axioms scalar_inverse_bridge
#print axioms zero_not_in_domain
#print axioms conjecture2353_false
#print axioms fieldThree
end Conjecture2353
