import Std

/-! Conjecture 425: the cube with side length two already violates log-concavity.
All four entries range over 0,1,2.  Enumeration completeness, monotonicity,
volumes, and the coefficient inequality are checked by the Lean kernel. -/
namespace Conjecture425

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Entries are top-left, top-right, bottom-left, bottom-right. -/
abbrev Grid := Fin 3 × Fin 3 × Fin 3 × Fin 3

/-- Standard weak decrease along rows and columns of a plane partition. -/
def IsPlanePartition (g : Grid) : Prop :=
  g.1 ≥ g.2.1 ∧ g.1 ≥ g.2.2.1 ∧ g.2.1 ≥ g.2.2.2 ∧ g.2.2.1 ≥ g.2.2.2

instance (g : Grid) : Decidable (IsPlanePartition g) := inferInstanceAs
  (Decidable (_ ∧ _ ∧ _ ∧ _))

def volume (g : Grid) : Nat :=
  g.1.val + g.2.1.val + g.2.2.1.val + g.2.2.2.val

def allGrids : List Grid :=
  (List.finRange 3).flatMap fun a =>
  (List.finRange 3).flatMap fun b =>
  (List.finRange 3).flatMap fun c =>
  (List.finRange 3).map fun d => (a,b,c,d)

/-- The enumeration contains every possible bounded 2 by 2 array. -/
theorem allGrids_complete : ∀ a b c d : Fin 3, (a,b,c,d) ∈ allGrids := by decide

/-- Each array is counted once. -/
theorem allGrids_nodup : allGrids.Nodup := by decide

def planePartitions : List Grid := allGrids.filter (fun g => decide (IsPlanePartition g))

/-- The filtered objects are exactly the plane partitions in the 2 by 2 by 2 box. -/
theorem membership_exact : ∀ a b c d : Fin 3,
    ((a,b,c,d) ∈ planePartitions ↔ IsPlanePartition (a,b,c,d)) := by decide

/-- Coefficient of q^k in the volume generating function of this cubic box. -/
def coefficient (k : Nat) : Nat :=
  (planePartitions.filter (fun g => decide (volume g = k))).length

def LogConcave (a : Nat → Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → a k * a k ≥ a (k-1) * a (k+1)

theorem full_coefficient_list :
    (List.range 9).map coefficient = [1,1,3,3,4,3,3,1,1] := by decide

theorem coefficient_zero : coefficient 0 = 1 := by decide
theorem coefficient_one : coefficient 1 = 1 := by decide
theorem coefficient_two : coefficient 2 = 3 := by decide

/-- A diagonal (equal side lengths) box with a coefficient sequence
that fails the claimed universal log-concavity. -/
theorem conjecture425_counterexample : ¬ LogConcave coefficient := by
  intro h
  have bad := h 1 (by decide)
  have impossible : ¬ (coefficient 1 * coefficient 1 ≥
      coefficient (1-1) * coefficient (1+1)) := by decide
  exact impossible bad

#print axioms allGrids_complete
#print axioms allGrids_nodup
#print axioms membership_exact
#print axioms full_coefficient_list
#print axioms conjecture425_counterexample
end Conjecture425

/-! A direct bridge to the exact MacMahon product. A formal power series is
represented by its integer coefficients. Multiplication is the Cauchy
convolution; the displayed product is defined by its numerator and denominator,
without assuming MacMahon's counting theorem. -/
namespace Conjecture425

abbrev Series := Nat → Int

def seriesOne : Series := fun n => if n = 0 then 1 else 0

def seriesMul (a b : Series) : Series := fun n =>
  ((List.range (n + 1)).map fun i => a (n - i) * b i).sum

def oneMinusPower (k : Nat) : Series := fun n =>
  (if n = 0 then 1 else 0) - (if n = k then 1 else 0)

def cubeFactors (n shift : Nat) : List Series :=
  (List.range n).flatMap fun i =>
  (List.range n).flatMap fun j =>
  (List.range n).map fun k => oneMinusPower (i + j + k + shift)

def seriesProduct (factors : List Series) : Series :=
  factors.foldr seriesMul seriesOne

/-- With indices 0,...,n-1, the numerator exponent is i+j+k+2
and the denominator exponent is i+j+k+1. These are exactly the usual
one-based exponents i+j+k-1 and i+j+k-2. -/
def macMahonNumerator (n : Nat) : Series := seriesProduct (cubeFactors n 2)
def macMahonDenominator (n : Nat) : Series := seriesProduct (cubeFactors n 1)

/-- Coefficients of the rational MacMahon product, interpreted as formal
power series: denominator * F = numerator. The denominator's constant
coefficient is one, so formal division is valid and coefficients are unique. -/
def IsMacMahonCubeSeries (n : Nat) (f : Series) : Prop :=
  ∀ k, seriesMul (macMahonDenominator n) f k = macMahonNumerator n k

def SeriesLogConcave (f : Series) : Prop :=
  ∀ k : Nat, 1 ≤ k → f k * f k ≥ f (k - 1) * f (k + 1)

/-- Construct formal division by a series with constant coefficient one.
Every recursive call uses a strictly smaller coefficient index. -/
def formalQuotient (d p : Series) (k : Nat) : Int :=
  p k - ((List.range k).attach.map
    (fun i => d (k - i.val) * formalQuotient d p i.val)).sum
termination_by k
decreasing_by exact List.mem_range.mp i.property

theorem int_sum_append (xs ys : List Int) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.sum_cons, ih, Int.add_assoc]

theorem formalQuotient_spec (d p : Series) (h : d 0 = 1) (k : Nat) :
    seriesMul d (formalQuotient d p) k = p k := by
  have hq : formalQuotient d p k = p k -
      ((List.range k).map (fun i => d (k-i) * formalQuotient d p i)).sum := by
    rw [formalQuotient]
    simp
  simp only [seriesMul, List.range_succ, List.map_append, int_sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.sub_self, h, Int.one_mul, Int.add_zero]
  rw [hq]
  omega

theorem cube_two_denominator_prefix :
    macMahonDenominator 2 0 = 1 ∧
    macMahonDenominator 2 1 = -1 ∧
    macMahonDenominator 2 2 = -3 := by decide

theorem cube_two_numerator_prefix :
    macMahonNumerator 2 0 = 1 ∧
    macMahonNumerator 2 1 = 0 ∧
    macMahonNumerator 2 2 = -1 := by decide

theorem macmahon_cube_two_coefficients (f : Series)
    (hf : IsMacMahonCubeSeries 2 f) : f 0 = 1 ∧ f 1 = 1 ∧ f 2 = 3 := by
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  rcases cube_two_denominator_prefix with ⟨d0, d1, d2⟩
  rcases cube_two_numerator_prefix with ⟨n0, n1, n2⟩
  simp [seriesMul, List.range_succ, d0, n0] at h0
  simp [seriesMul, List.range_succ, d0, d1, n1, h0] at h1
  simp [seriesMul, List.range_succ, d0, d1, d2, n2, h0, h1] at h2
  omega

/-- The disproof now applies directly to any coefficient sequence of the
specified MacMahon product, not only to an independently defined enumerator. -/
theorem macmahon_cube_two_not_logconcave (f : Series)
    (hf : IsMacMahonCubeSeries 2 f) : ¬SeriesLogConcave f := by
  rcases macmahon_cube_two_coefficients f hf with ⟨h0, h1, h2⟩
  intro h
  have bad := h 1 (by decide)
  simp [h0, h1, h2] at bad

theorem counting_matches_macmahon_prefix (f : Series)
    (hf : IsMacMahonCubeSeries 2 f) :
    f 0 = Int.ofNat (coefficient 0) ∧
    f 1 = Int.ofNat (coefficient 1) ∧
    f 2 = Int.ofNat (coefficient 2) := by
  simpa [coefficient_zero, coefficient_one, coefficient_two]
    using macmahon_cube_two_coefficients f hf

/-- An actual infinite coefficient sequence exists; the preceding disproof
does not rely on a possibly empty predicate. -/
def macMahonCubeTwo : Series :=
  formalQuotient (macMahonDenominator 2) (macMahonNumerator 2)

theorem macMahonCubeTwo_spec : IsMacMahonCubeSeries 2 macMahonCubeTwo :=
  formalQuotient_spec _ _ cube_two_denominator_prefix.1

theorem macmahon_product_counterexample : ¬SeriesLogConcave macMahonCubeTwo :=
  macmahon_cube_two_not_logconcave macMahonCubeTwo macMahonCubeTwo_spec

#print axioms cube_two_denominator_prefix
#print axioms cube_two_numerator_prefix
#print axioms macmahon_cube_two_coefficients
#print axioms macmahon_cube_two_not_logconcave
#print axioms counting_matches_macmahon_prefix
#print axioms formalQuotient_spec
#print axioms macMahonCubeTwo_spec
#print axioms macmahon_product_counterexample
end Conjecture425
