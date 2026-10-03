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


namespace Conjecture425
/-! Finite prefixes are used only to compute coefficients efficiently.
Every prefix operation is proved to agree with the actual infinite-series
operation at each index below the specified cutoff. -/

def listSeries (p : List Int) : Series := fun k => p[k]?.getD 0
def prefixList (N : Nat) (f : Series) : List Int := (List.range N).map f

theorem prefixList_correct (N : Nat) (f : Series) (k : Nat) (hk : k < N) :
    listSeries (prefixList N f) k = f k := by
  simp [listSeries, prefixList, hk]

def PrefixEq (N : Nat) (f g : Series) : Prop := ∀ k, k < N → f k = g k

theorem seriesMul_prefix (N : Nat) (a b c d : Series)
    (ha : PrefixEq N a c) (hb : PrefixEq N b d) :
    PrefixEq N (seriesMul a b) (seriesMul c d) := by
  intro k hk
  unfold seriesMul
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < k + 1 := List.mem_range.mp hi
  rw [ha (k-i) (by omega), hb i (by omega)]

def prefixMul (N : Nat) (a b : List Int) : List Int :=
  prefixList N (seriesMul (listSeries a) (listSeries b))

def prefixProduct (N : Nat) (fs : List Series) : List Int :=
  fs.foldr (fun f p => prefixMul N (prefixList N f) p) (prefixList N seriesOne)

theorem prefixProduct_correct (N : Nat) (fs : List Series) :
    PrefixEq N (listSeries (prefixProduct N fs)) (seriesProduct fs) := by
  induction fs with
  | nil =>
    intro k hk
    exact prefixList_correct N seriesOne k hk
  | cons f fs ih =>
    intro k hk
    change listSeries (prefixMul N (prefixList N f) (prefixProduct N fs)) k =
      seriesMul f (seriesProduct fs) k
    rw [prefixMul, prefixList_correct N _ k hk]
    exact seriesMul_prefix N _ _ _ _
      (fun i hi => prefixList_correct N f i hi) ih k hk

def cubeNumeratorPrefix (n : Nat) : List Int := prefixProduct 29 (cubeFactors n 2)
def cubeDenominatorPrefix (n : Nat) : List Int := prefixProduct 29 (cubeFactors n 1)

theorem cubeNumeratorPrefix_correct (n k : Nat) (hk : k < 29) :
    listSeries (cubeNumeratorPrefix n) k = macMahonNumerator n k :=
  prefixProduct_correct 29 (cubeFactors n 2) k hk

theorem cubeDenominatorPrefix_correct (n k : Nat) (hk : k < 29) :
    listSeries (cubeDenominatorPrefix n) k = macMahonDenominator n k :=
  prefixProduct_correct 29 (cubeFactors n 1) k hk

end Conjecture425

namespace Conjecture425

private theorem numerator1_stage0 : prefixProduct 29 [] = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by decide
private theorem numerator1_stage1 :
    prefixProduct 29 [oneMinusPower 2] =
      [1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 2))
    (prefixProduct 29 []) = _
  rw [numerator1_stage0]
  decide

def numerator1Table : List Int := [1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

theorem cubeNumerator1_table : cubeNumeratorPrefix 1 = numerator1Table :=
  numerator1_stage1

private theorem denominator1_stage0 : prefixProduct 29 [] = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by decide
private theorem denominator1_stage1 :
    prefixProduct 29 [oneMinusPower 1] =
      [1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 1))
    (prefixProduct 29 []) = _
  rw [denominator1_stage0]
  decide

def denominator1Table : List Int := [1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

theorem cubeDenominator1_table : cubeDenominatorPrefix 1 = denominator1Table :=
  denominator1_stage1

private theorem numerator2_stage0 : prefixProduct 29 [] = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by decide
private theorem numerator2_stage1 :
    prefixProduct 29 [oneMinusPower 5] =
      [1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 []) = _
  rw [numerator2_stage0]
  decide
private theorem numerator2_stage2 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5] =
      [1,0,0,0,-1,-1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5]) = _
  rw [numerator2_stage1]
  decide
private theorem numerator2_stage3 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 4, oneMinusPower 5] =
      [1,0,0,0,-2,-1,0,0,1,2,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5]) = _
  rw [numerator2_stage2]
  decide
private theorem numerator2_stage4 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 4, oneMinusPower 5] =
      [1,0,0,-1,-2,-1,0,2,2,2,0,-1,-2,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 4, oneMinusPower 5]) = _
  rw [numerator2_stage3]
  decide
private theorem numerator2_stage5 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 4, oneMinusPower 5] =
      [1,0,0,-1,-3,-1,0,3,4,3,0,-3,-4,-3,0,1,3,1,0,0,-1,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 4, oneMinusPower 5]) = _
  rw [numerator2_stage4]
  decide
private theorem numerator2_stage6 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 4, oneMinusPower 5] =
      [1,0,0,-2,-3,-1,1,6,5,3,-3,-7,-7,-3,3,5,6,1,-1,-3,-2,0,0,1,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 4, oneMinusPower 5]) = _
  rw [numerator2_stage5]
  decide
private theorem numerator2_stage7 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 4, oneMinusPower 5] =
      [1,0,0,-3,-3,-1,3,9,6,2,-9,-12,-10,0,10,12,9,-2,-6,-9,-3,1,3,3,0,0,-1,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 4, oneMinusPower 5]) = _
  rw [numerator2_stage6]
  decide
private theorem numerator2_stage8 :
    prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 4, oneMinusPower 5] =
      [1,0,-1,-3,-3,2,6,10,3,-7,-15,-14,-1,12,20,12,-1,-14,-15,-7,3,10,6,2,-3,-3,-1,0,1] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 2))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 4, oneMinusPower 5]) = _
  rw [numerator2_stage7]
  decide

def numerator2Table : List Int := [1,0,-1,-3,-3,2,6,10,3,-7,-15,-14,-1,12,20,12,-1,-14,-15,-7,3,10,6,2,-3,-3,-1,0,1]

theorem cubeNumerator2_table : cubeNumeratorPrefix 2 = numerator2Table :=
  numerator2_stage8

private theorem denominator2_stage0 : prefixProduct 29 [] = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by decide
private theorem denominator2_stage1 :
    prefixProduct 29 [oneMinusPower 4] =
      [1,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 []) = _
  rw [denominator2_stage0]
  decide
private theorem denominator2_stage2 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4] =
      [1,0,0,-1,-1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4]) = _
  rw [denominator2_stage1]
  decide
private theorem denominator2_stage3 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 3, oneMinusPower 4] =
      [1,0,0,-2,-1,0,1,2,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4]) = _
  rw [denominator2_stage2]
  decide
private theorem denominator2_stage4 :
    prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4] =
      [1,0,-1,-2,-1,2,2,2,-1,-2,-1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 2))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 3, oneMinusPower 4]) = _
  rw [denominator2_stage3]
  decide
private theorem denominator2_stage5 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4] =
      [1,0,-1,-3,-1,3,4,3,-3,-4,-3,1,3,1,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4]) = _
  rw [denominator2_stage4]
  decide
private theorem denominator2_stage6 :
    prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4] =
      [1,0,-2,-3,0,6,5,0,-7,-7,0,5,6,0,-3,-2,0,1,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 2))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4]) = _
  rw [denominator2_stage5]
  decide
private theorem denominator2_stage7 :
    prefixProduct 29 [oneMinusPower 2, oneMinusPower 2, oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4] =
      [1,0,-3,-3,2,9,5,-6,-12,-7,7,12,6,-5,-9,-2,3,3,0,-1,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 2))
    (prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4]) = _
  rw [denominator2_stage6]
  decide
private theorem denominator2_stage8 :
    prefixProduct 29 [oneMinusPower 1, oneMinusPower 2, oneMinusPower 2, oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4] =
      [1,-1,-3,0,5,7,-4,-11,-6,5,14,5,-6,-11,-4,7,5,0,-3,-1,1,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 1))
    (prefixProduct 29 [oneMinusPower 2, oneMinusPower 2, oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 3, oneMinusPower 4]) = _
  rw [denominator2_stage7]
  decide

def denominator2Table : List Int := [1,-1,-3,0,5,7,-4,-11,-6,5,14,5,-6,-11,-4,7,5,0,-3,-1,1,0,0,0,0,0,0,0,0]

theorem cubeDenominator2_table : cubeDenominatorPrefix 2 = denominator2Table :=
  denominator2_stage8

private theorem numerator3_stage0 : prefixProduct 29 [] = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by decide
private theorem numerator3_stage1 :
    prefixProduct 29 [oneMinusPower 8] =
      [1,0,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 8))
    (prefixProduct 29 []) = _
  rw [numerator3_stage0]
  decide
private theorem numerator3_stage2 :
    prefixProduct 29 [oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,0,0,0,-1,-1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 7))
    (prefixProduct 29 [oneMinusPower 8]) = _
  rw [numerator3_stage1]
  decide
private theorem numerator3_stage3 :
    prefixProduct 29 [oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,0,0,-1,-1,-1,0,0,0,0,1,1,1,0,0,0,0,0,-1,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 6))
    (prefixProduct 29 [oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage2]
  decide
private theorem numerator3_stage4 :
    prefixProduct 29 [oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,0,0,-1,-2,-1,0,0,0,0,2,2,2,0,0,0,0,-1,-2,-1,0,0,0,0,0,1] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 7))
    (prefixProduct 29 [oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage3]
  decide
private theorem numerator3_stage5 :
    prefixProduct 29 [oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,0,0,-2,-2,-1,0,0,0,1,4,3,2,0,0,0,-2,-3,-4,-1,0,0,0,1,2,2] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 6))
    (prefixProduct 29 [oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage4]
  decide
private theorem numerator3_stage6 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,0,-1,-2,-2,-1,0,0,2,3,5,3,2,0,-1,-4,-5,-5,-4,-1,0,2,3,5,3,2] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage5]
  decide
private theorem numerator3_stage7 :
    prefixProduct 29 [oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,0,-1,-3,-2,-1,0,0,3,5,7,4,2,0,-3,-7,-10,-8,-6,-1,1,6,8,10,7,3] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 6))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage6]
  decide
private theorem numerator3_stage8 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,0,-2,-3,-2,-1,0,1,6,7,8,4,2,-3,-8,-14,-14,-10,-6,2,8,16,16,16,8,2] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage7]
  decide
private theorem numerator3_stage9 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,-1,-2,-3,-2,-1,2,4,8,8,8,3,-4,-10,-16,-18,-16,-7,2,16,22,26,22,14,0,-14] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage8]
  decide
private theorem numerator3_stage10 :
    prefixProduct 29 [oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,-1,-2,-3,-3,-1,2,4,9,10,11,5,-3,-12,-20,-26,-24,-15,-1,20,32,42,40,30,7,-16] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 7))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage9]
  decide
private theorem numerator3_stage11 :
    prefixProduct 29 [oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,-1,-2,-4,-3,-1,2,5,11,13,14,6,-5,-16,-29,-36,-35,-20,2,32,52,68,64,45,8,-36] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 6))
    (prefixProduct 29 [oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage10]
  decide
private theorem numerator3_stage12 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,-1,-3,-4,-3,-1,3,7,15,16,15,4,-10,-27,-42,-50,-41,-15,18,61,88,103,84,43,-24,-88] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage11]
  decide
private theorem numerator3_stage13 :
    prefixProduct 29 [oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,-1,-3,-5,-3,-1,3,8,18,20,18,5,-13,-34,-57,-66,-56,-19,28,88,130,153,125,58,-42,-149] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 6))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage12]
  decide
private theorem numerator3_stage14 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,-1,-4,-5,-3,-1,4,11,23,23,19,2,-21,-52,-77,-84,-61,-6,62,145,196,209,144,30,-130,-279] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage13]
  decide
private theorem numerator3_stage15 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,-2,-4,-5,-3,0,8,16,26,24,15,-9,-44,-75,-96,-86,-40,46,139,229,257,215,82,-115,-326,-488] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage14]
  decide
private theorem numerator3_stage16 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,-2,-5,-5,-3,0,10,20,31,27,15,-17,-60,-101,-120,-101,-31,90,214,325,343,255,36,-254,-555,-745] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage15]
  decide
private theorem numerator3_stage17 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,0,-3,-5,-5,-3,2,15,25,34,27,5,-37,-91,-128,-135,-84,29,191,334,426,374,165,-178,-579,-898,-1000] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage16]
  decide
private theorem numerator3_stage18 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,-1,-3,-5,-5,0,7,20,28,32,12,-20,-71,-118,-133,-98,7,157,326,418,397,183,-169,-604,-953,-1063,-822] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage17]
  decide
private theorem numerator3_stage19 :
    prefixProduct 29 [oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,-1,-3,-5,-6,0,7,21,31,37,17,-20,-78,-138,-161,-130,-5,177,397,536,530,281,-176,-761,-1279,-1481,-1219] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 6))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage18]
  decide
private theorem numerator3_stage20 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,-1,-3,-6,-6,0,8,24,36,43,17,-27,-99,-169,-198,-147,15,255,535,697,660,286,-353,-1158,-1815,-2011,-1500] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage19]
  decide
private theorem numerator3_stage21 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,-1,-4,-6,-6,1,11,30,42,43,9,-51,-135,-212,-215,-120,114,424,733,844,645,31,-888,-1855,-2475,-2297,-1147] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage20]
  decide
private theorem numerator3_stage22 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,-1,-4,-7,-6,1,12,34,48,49,8,-62,-165,-254,-258,-129,165,559,945,1059,765,-83,-1312,-2588,-3319,-2942,-1178] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage21]
  decide
private theorem numerator3_stage23 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,-1,-5,-7,-6,2,16,41,54,48,-4,-96,-213,-303,-266,-67,330,813,1203,1188,600,-642,-2257,-3647,-4084,-2859,134] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage22]
  decide
private theorem numerator3_stage24 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,-2,-5,-7,-5,7,23,47,52,32,-45,-150,-261,-299,-170,146,633,1079,1270,858,-213,-1845,-3445,-4247,-3442,-602,3781] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage23]
  decide
private theorem numerator3_stage25 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,-2,-6,-7,-5,9,28,54,57,25,-68,-197,-313,-331,-125,296,894,1378,1440,712,-846,-2924,-4715,-5105,-3229,1243,7226] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage24]
  decide
private theorem numerator3_stage26 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,0,-3,-6,-7,-3,15,35,59,48,-3,-122,-254,-338,-263,72,609,1225,1503,1144,-182,-2224,-4364,-5427,-4259,-305,5958,12331] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage25]
  decide
private theorem numerator3_stage27 :
    prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8] =
      [1,0,-1,-3,-6,-4,3,22,38,44,13,-62,-170,-251,-216,-9,410,872,1153,894,-81,-1685,-3368,-4182,-3203,105,5122,10217,12636] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 2))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7, oneMinusPower 6, oneMinusPower 7, oneMinusPower 8]) = _
  rw [numerator3_stage26]
  decide

def numerator3Table : List Int := [1,0,-1,-3,-6,-4,3,22,38,44,13,-62,-170,-251,-216,-9,410,872,1153,894,-81,-1685,-3368,-4182,-3203,105,5122,10217,12636]

theorem cubeNumerator3_table : cubeNumeratorPrefix 3 = numerator3Table :=
  numerator3_stage27

private theorem denominator3_stage0 : prefixProduct 29 [] = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by decide
private theorem denominator3_stage1 :
    prefixProduct 29 [oneMinusPower 7] =
      [1,0,0,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 7))
    (prefixProduct 29 []) = _
  rw [denominator3_stage0]
  decide
private theorem denominator3_stage2 :
    prefixProduct 29 [oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,0,0,0,-1,-1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 6))
    (prefixProduct 29 [oneMinusPower 7]) = _
  rw [denominator3_stage1]
  decide
private theorem denominator3_stage3 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,0,0,-1,-1,-1,0,0,0,1,1,1,0,0,0,0,-1,0,0,0,0,0,0,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage2]
  decide
private theorem denominator3_stage4 :
    prefixProduct 29 [oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,0,0,-1,-2,-1,0,0,0,2,2,2,0,0,0,-1,-2,-1,0,0,0,0,1,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 6))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage3]
  decide
private theorem denominator3_stage5 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,0,0,-2,-2,-1,0,0,1,4,3,2,0,0,-2,-3,-4,-1,0,0,1,2,2,0,0,0,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage4]
  decide
private theorem denominator3_stage6 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,0,-1,-2,-2,-1,0,2,3,5,3,2,-1,-4,-5,-5,-4,-1,2,3,5,3,2,0,-1,-2,-2] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage5]
  decide
private theorem denominator3_stage7 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,0,-1,-3,-2,-1,0,3,5,7,4,2,-3,-7,-10,-8,-6,0,6,8,10,7,3,-2,-4,-7,-5] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage6]
  decide
private theorem denominator3_stage8 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,0,-2,-3,-2,-1,1,6,7,8,4,-1,-8,-14,-14,-10,-3,7,16,16,16,7,-3,-10,-14,-14,-8] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage7]
  decide
private theorem denominator3_stage9 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,-1,-2,-3,-2,1,4,8,8,7,-2,-8,-16,-18,-13,-2,11,21,26,19,9,-9,-19,-26,-21,-11,2] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage8]
  decide
private theorem denominator3_stage10 :
    prefixProduct 29 [oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,-1,-2,-3,-3,1,4,9,10,10,0,-9,-20,-26,-21,-9,13,29,42,37,22,-7,-30,-47,-47,-30,-7] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 6))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage9]
  decide
private theorem denominator3_stage11 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,-1,-2,-4,-3,1,5,11,13,13,-1,-13,-29,-36,-31,-9,22,49,68,58,31,-20,-59,-89,-84,-52,0] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage10]
  decide
private theorem denominator3_stage12 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,-1,-3,-4,-3,2,7,15,16,12,-6,-24,-42,-49,-30,4,51,85,99,67,9,-69,-127,-147,-115,-32,59] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage11]
  decide
private theorem denominator3_stage13 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,-1,-3,-5,-3,2,8,18,20,15,-8,-31,-57,-65,-42,10,75,127,148,97,5,-120,-212,-246,-182,-41,128] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage12]
  decide
private theorem denominator3_stage14 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,-1,-4,-5,-3,3,11,23,23,13,-16,-49,-77,-80,-34,41,132,192,190,87,-70,-247,-360,-343,-187,79,340] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage13]
  decide
private theorem denominator3_stage15 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,-2,-4,-5,-2,7,16,26,20,2,-39,-72,-90,-64,15,118,212,226,149,-45,-262,-437,-447,-273,60,439,683] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage14]
  decide
private theorem denominator3_stage16 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,-2,-5,-5,-2,9,20,31,22,-5,-55,-98,-110,-66,54,190,302,290,134,-163,-474,-663,-596,-228,322,876,1130] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage15]
  decide
private theorem denominator3_stage17 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,0,-3,-5,-5,0,14,25,33,13,-25,-86,-120,-105,-11,152,300,368,236,-56,-465,-764,-797,-433,246,985,1472,1358] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage16]
  decide
private theorem denominator3_stage18 :
    prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,-1,-3,-5,-2,5,19,25,19,-12,-58,-99,-95,-19,109,257,311,216,-64,-424,-701,-708,-332,331,1043,1418,1226,373] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 2))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage17]
  decide
private theorem denominator3_stage19 :
    prefixProduct 29 [oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,-1,-3,-5,-3,5,20,28,24,-10,-63,-118,-120,-38,121,315,410,311,-45,-533,-958,-1019,-548,395,1467,2119,1934,705] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 5))
    (prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage18]
  decide
private theorem denominator3_stage20 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,-1,-3,-6,-3,6,23,33,27,-15,-83,-146,-144,-28,184,433,530,349,-166,-848,-1368,-1330,-503,928,2425,3138,2482,310] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage19]
  decide
private theorem denominator3_stage21 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,-1,-4,-6,-2,9,29,36,21,-38,-116,-173,-129,55,330,577,558,165,-599,-1378,-1717,-1164,345,2296,3755,3641,1554,-2115] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage20]
  decide
private theorem denominator3_stage22 :
    prefixProduct 29 [oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,-1,-4,-7,-2,10,33,42,23,-47,-145,-209,-150,93,446,750,687,110,-929,-1955,-2275,-1329,944,3674,5472,4805,1209,-4411] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 4))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage21]
  decide
private theorem denominator3_stage23 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,-1,-5,-7,-1,14,40,44,13,-80,-187,-232,-103,238,655,900,594,-336,-1679,-2642,-2385,-400,2899,5949,6801,3861,-2465,-9883] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage22]
  decide
private theorem denominator3_stage24 :
    prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,-2,-5,-6,4,21,41,30,-27,-124,-200,-152,84,470,758,662,-61,-1236,-2273,-2306,-706,2242,5284,6349,3902,-2088,-9266,-13744] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 2))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage23]
  decide
private theorem denominator3_stage25 :
    prefixProduct 29 [oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,-2,-6,-6,6,26,47,26,-48,-165,-230,-125,208,670,910,578,-531,-1994,-2935,-2245,530,4515,7590,7055,1660,-7372,-15615,-17646] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 3))
    (prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage24]
  decide
private theorem denominator3_stage26 :
    prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,0,-3,-6,-4,12,32,41,0,-95,-191,-182,40,438,795,702,-92,-1441,-2572,-2404,-251,3465,6760,7060,2540,-5930,-14427,-17275,-10274] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 2))
    (prefixProduct 29 [oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage25]
  decide
private theorem denominator3_stage27 :
    prefixProduct 29 [oneMinusPower 1, oneMinusPower 2, oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7] =
      [1,-1,-3,-3,2,16,20,9,-41,-95,-96,9,222,398,357,-93,-794,-1349,-1131,168,2153,3716,3295,300,-4520,-8470,-8497,-2848,7001] := by
  change prefixMul 29 (prefixList 29 (oneMinusPower 1))
    (prefixProduct 29 [oneMinusPower 2, oneMinusPower 3, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 2, oneMinusPower 3, oneMinusPower 4, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 3, oneMinusPower 4, oneMinusPower 5, oneMinusPower 4, oneMinusPower 5, oneMinusPower 6, oneMinusPower 5, oneMinusPower 6, oneMinusPower 7]) = _
  rw [denominator3_stage26]
  decide

def denominator3Table : List Int := [1,-1,-3,-3,2,16,20,9,-41,-95,-96,9,222,398,357,-93,-794,-1349,-1131,168,2153,3716,3295,300,-4520,-8470,-8497,-2848,7001]

theorem cubeDenominator3_table : cubeDenominatorPrefix 3 = denominator3Table :=
  denominator3_stage27

def cube1Coefficients : List Int := [1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

theorem cube1_table_identity : ∀ k : Fin 29,
    listSeries (prefixMul 29 denominator1Table cube1Coefficients) k.val =
      listSeries numerator1Table k.val := by decide

def cube2Coefficients : List Int := [1,1,3,3,4,3,3,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

theorem cube2_table_identity : ∀ k : Fin 29,
    listSeries (prefixMul 29 denominator2Table cube2Coefficients) k.val =
      listSeries numerator2Table k.val := by decide

def cube3Coefficients : List Int := [1,1,3,6,10,15,24,32,43,54,64,73,81,83,83,81,73,64,54,43,32,24,15,10,6,3,1,1,0]

theorem cube3_table_identity : ∀ k : Fin 29,
    listSeries (prefixMul 29 denominator3Table cube3Coefficients) k.val =
      listSeries numerator3Table k.val := by decide

end Conjecture425


namespace Conjecture425

theorem equation_prefix_unique (N : Nat) (d p f g : Series)
    (hd : d 0 = 1)
    (hf : ∀ k, seriesMul d f k = p k)
    (hg : ∀ k, k < N → seriesMul d g k = p k) : PrefixEq N f g := by
  intro k hk
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have hs : ((List.range k).map (fun i => d (k-i) * f i)).sum =
        ((List.range k).map (fun i => d (k-i) * g i)).sum := by
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [ih i (List.mem_range.mp hi) (by have := List.mem_range.mp hi; omega)]
    have hfk := hf k
    have hgk := hg k hk
    simp only [seriesMul, List.range_succ, List.map_append, int_sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.sub_self, hd, Int.one_mul, Int.add_zero] at hfk hgk
    rw [hs] at hfk
    omega

theorem cube_prefix_equation (n : Nat) (cs : List Int)
    (h : ∀ k : Fin 29,
      listSeries (prefixMul 29 (cubeDenominatorPrefix n) cs) k.val =
        listSeries (cubeNumeratorPrefix n) k.val) :
    ∀ k, k < 29 →
      seriesMul (macMahonDenominator n) (listSeries cs) k = macMahonNumerator n k := by
  intro k hk
  have hc := h ⟨k,hk⟩
  change listSeries (prefixMul 29 (cubeDenominatorPrefix n) cs) k =
    listSeries (cubeNumeratorPrefix n) k at hc
  rw [prefixMul, prefixList_correct 29 _ k hk,
    cubeNumeratorPrefix_correct n k hk] at hc
  have heq := seriesMul_prefix 29 (listSeries (cubeDenominatorPrefix n))
    (listSeries cs) (macMahonDenominator n) (listSeries cs)
    (fun i hi => cubeDenominatorPrefix_correct n i hi) (fun _ _ => rfl) k hk
  rw [heq] at hc
  exact hc

theorem cube_one_denominator_constant : macMahonDenominator 1 0 = 1 := by decide

theorem cube_three_denominator_constant : macMahonDenominator 3 0 = 1 := by
  rw [← cubeDenominatorPrefix_correct 3 0 (by decide), cubeDenominator3_table]
  decide

def macMahonCubeOne : Series :=
  formalQuotient (macMahonDenominator 1) (macMahonNumerator 1)

def macMahonCubeThree : Series :=
  formalQuotient (macMahonDenominator 3) (macMahonNumerator 3)

theorem macMahonCubeOne_spec : IsMacMahonCubeSeries 1 macMahonCubeOne :=
  formalQuotient_spec _ _ cube_one_denominator_constant

theorem macMahonCubeThree_spec : IsMacMahonCubeSeries 3 macMahonCubeThree :=
  formalQuotient_spec _ _ cube_three_denominator_constant

theorem cube_one_coefficients (f : Series) (hf : IsMacMahonCubeSeries 1 f) :
    PrefixEq 29 f (listSeries cube1Coefficients) := by
  apply equation_prefix_unique 29 _ _ _ _ cube_one_denominator_constant hf
  apply cube_prefix_equation
  rw [cubeDenominator1_table, cubeNumerator1_table]
  exact cube1_table_identity

theorem cube_two_coefficients (f : Series) (hf : IsMacMahonCubeSeries 2 f) :
    PrefixEq 29 f (listSeries cube2Coefficients) := by
  apply equation_prefix_unique 29 _ _ _ _ cube_two_denominator_prefix.1 hf
  apply cube_prefix_equation
  rw [cubeDenominator2_table, cubeNumerator2_table]
  exact cube2_table_identity

theorem cube_three_coefficients (f : Series) (hf : IsMacMahonCubeSeries 3 f) :
    PrefixEq 29 f (listSeries cube3Coefficients) := by
  apply equation_prefix_unique 29 _ _ _ _ cube_three_denominator_constant hf
  apply cube_prefix_equation
  rw [cubeDenominator3_table, cubeNumerator3_table]
  exact cube3_table_identity

/-- The coefficient is calculated from the actual MacMahon products,
not from an independently asserted degree or leading-coefficient formula. -/
theorem macmahon_cross_size_coefficient (f1 f2 f3 : Series)
    (h1 : IsMacMahonCubeSeries 1 f1)
    (h2 : IsMacMahonCubeSeries 2 f2)
    (h3 : IsMacMahonCubeSeries 3 f3) :
    seriesMul f2 f2 28 - seriesMul f1 f3 28 = -1 := by
  have e1 := cube_one_coefficients f1 h1
  have e2 := cube_two_coefficients f2 h2
  have e3 := cube_three_coefficients f3 h3
  rw [seriesMul_prefix 29 _ _ _ _ e2 e2 28 (by decide),
      seriesMul_prefix 29 _ _ _ _ e1 e3 28 (by decide)]
  decide

/-- The n=2 necessary instance of coefficientwise log-concavity of F_n(q). -/
def CrossSizeLogConcave (f1 f2 f3 : Series) : Prop :=
  ∀ k, seriesMul f1 f3 k ≤ seriesMul f2 f2 k

theorem macmahon_cross_size_not_logconcave (f1 f2 f3 : Series)
    (h1 : IsMacMahonCubeSeries 1 f1)
    (h2 : IsMacMahonCubeSeries 2 f2)
    (h3 : IsMacMahonCubeSeries 3 f3) : ¬CrossSizeLogConcave f1 f2 f3 := by
  intro h
  have hbad := macmahon_cross_size_coefficient f1 f2 f3 h1 h2 h3
  have h28 := h 28
  omega

/-- The universal claim over consecutive actual MacMahon quotients. -/
def DiagonalCoefficientwiseLogConcavity : Prop :=
  ∀ n, 1 ≤ n → ∀ fprev fcur fnext : Series,
    IsMacMahonCubeSeries (n-1) fprev →
    IsMacMahonCubeSeries n fcur →
    IsMacMahonCubeSeries (n+1) fnext →
    CrossSizeLogConcave fprev fcur fnext

theorem macmahon_diagonal_coefficientwise_counterexample :
    ¬DiagonalCoefficientwiseLogConcavity := by
  intro h
  exact macmahon_cross_size_not_logconcave
    macMahonCubeOne macMahonCubeTwo macMahonCubeThree
    macMahonCubeOne_spec macMahonCubeTwo_spec macMahonCubeThree_spec
    (h 2 (by decide) _ _ _ macMahonCubeOne_spec macMahonCubeTwo_spec macMahonCubeThree_spec)

theorem concrete_cross_size_coefficient :
    seriesMul macMahonCubeTwo macMahonCubeTwo 28 -
      seriesMul macMahonCubeOne macMahonCubeThree 28 = -1 :=
  macmahon_cross_size_coefficient _ _ _
    macMahonCubeOne_spec macMahonCubeTwo_spec macMahonCubeThree_spec

#print axioms prefixProduct_correct
#print axioms equation_prefix_unique
#print axioms cube_one_coefficients
#print axioms cube_two_coefficients
#print axioms cube_three_coefficients
#print axioms macmahon_cross_size_coefficient
#print axioms concrete_cross_size_coefficient
#print axioms macmahon_diagonal_coefficientwise_counterexample

end Conjecture425
