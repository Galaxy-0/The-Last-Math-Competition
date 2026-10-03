import Std

namespace Conjecture6542
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

instance finiteExists (n : Nat) (P : Fin n → Prop) [DecidablePred P] : Decidable (∃ x, P x) :=
  decidable_of_iff (¬∀ x, ¬P x) (by
    constructor
    · intro h
      obtain ⟨x,hx⟩ := Classical.not_forall.mp h
      exact ⟨x,Classical.byContradiction hx⟩
    · rintro ⟨x,hx⟩ h
      exact h x hx)

abbrev Vertex := Fin 3
abbrev Dart := Fin 6
def adjacent (v w : Vertex) : Bool := decide (v ≠ w)
theorem triangle_graph_laws :
    (∀ v, adjacent v v = false) ∧ (∀ v w, adjacent v w = adjacent w v) := by decide

theorem triangle_connected_regular :
    (∀ v w, v=w ∨ adjacent v w = true) ∧
    (∀ v, ((List.finRange 3).filter (fun w => adjacent v w)).length = 2) := by decide

/-- Darts 0,1,2 run clockwise; 3,4,5 run counterclockwise. -/
def tail (d : Dart) : Vertex :=
  match d.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 2 | _ => 1
def head (d : Dart) : Vertex :=
  match d.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 2 | 4 => 1 | _ => 0
def reverse (d : Dart) : Dart :=
  match d.val with | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | _ => 0
def next (d : Dart) : Dart :=
  match d.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 4 | 4 => 5 | _ => 3
def direction (d : Dart) : Fin 2 := if d.val < 3 then 0 else 1

theorem all_oriented_edges :
    (∀ d, adjacent (tail d) (head d) = true) ∧
    (∀ v w, adjacent v w = true → ∃ d, tail d = v ∧ head d = w) ∧
    (∀ d e, tail d = tail e → head d = head e → d = e) ∧
    (∀ d, tail (reverse d) = head d ∧ head (reverse d) = tail d ∧ reverse (reverse d) = d) := by
  decide

/-- Admissible consecutive directed edges: incidence and no backtracking. -/
def Step (d e : Dart) : Prop := head d = tail e ∧ e ≠ reverse d
instance (d e : Dart) : Decidable (Step d e) := by unfold Step; infer_instance
theorem step_is_forced : ∀ d e, Step d e ↔ e = next d := by decide
theorem next_three : ∀ d, next (next (next d)) = d := by decide
theorem next_not_self : ∀ d, next d ≠ d := by decide
theorem next_two_not_self : ∀ d, next (next d) ≠ d := by decide
theorem next_direction : ∀ d, direction (next d) = direction d := by decide

def orbit (d : Dart) (n : Nat) : Dart :=
  if n % 3 = 0 then d else if n % 3 = 1 then next d else next (next d)
theorem orbit_zero (d : Dart) : orbit d 0 = d := rfl
theorem orbit_succ (d : Dart) (n : Nat) : orbit d (n+1) = next (orbit d n) := by
  have casesN : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases casesN with h | h | h
  · have hn : (n+1)%3=1 := by omega
    simp [orbit,h,hn]
  · have hn : (n+1)%3=2 := by omega
    simp [orbit,h,hn]
  · have hn : (n+1)%3=0 := by omega
    simp [orbit,h,hn,next_three]

theorem orbit_add (d : Dart) (s n : Nat) : orbit d (s+n) = orbit (orbit d s) n := by
  induction n with
  | zero => simp only [Nat.add_zero,orbit_zero]
  | succ n ih =>
    rw [← Nat.add_assoc,orbit_succ,ih,orbit_succ]

theorem orbit_return_iff (d : Dart) (n : Nat) : orbit d n = d ↔ n%3=0 := by
  have casesN : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases casesN with h | h | h
  · simp [orbit,h]
  · simp [orbit,h,next_not_self]
  · simp [orbit,h,next_two_not_self]

theorem orbit_period (d : Dart) (p : Nat) :
    (∀ n, orbit d (p+n) = orbit d n) ↔ p%3=0 := by
  constructor
  · intro h
    have h0 := h 0
    simp only [Nat.add_zero,orbit_zero] at h0
    exact (orbit_return_iff d p).mp h0
  · intro hp n
    rw [orbit_add,(orbit_return_iff d p).mpr hp]

theorem orbit_direction (d : Dart) (n : Nat) : direction (orbit d n) = direction d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [orbit_succ,next_direction,ih]

theorem every_reduced_walk_forced (f : Nat → Dart) (hs : ∀ n, Step (f n) (f (n+1))) :
    ∀ n, f n = orbit (f 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [(step_is_forced _ _).mp (hs n),ih,orbit_succ]

/-- A periodic directed walk. The step condition also crosses every period
boundary, so this is a closed, tailless, nonbacktracking walk. -/
structure ClosedWalk where
  length : Nat
  positive : 0 < length
  darts : Nat → Dart
  step : ∀ n, Step (darts n) (darts (n+1))
  periodic : ∀ n, darts (length+n) = darts n

/-- Every finite cyclic word with the usual wraparound nonbacktracking
condition extends to such a periodic walk; no lengths are omitted. -/
def fromFiniteWord (n : Nat) (hn : 0 < n) (f : Fin n → Dart)
    (hf : ∀ i : Fin n, Step (f i) (f ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩)) : ClosedWalk where
  length := n
  positive := hn
  darts i := f ⟨i%n,Nat.mod_lt _ hn⟩
  step i := by
    have h := hf ⟨i%n,Nat.mod_lt _ hn⟩
    have hi : ((i%n)+1)%n = (i+1)%n := by simp [Nat.add_mod]
    simpa only [hi] using h
  periodic i := by
    congr 1
    apply Fin.ext
    simp [Nat.add_mod]

theorem closed_walk_orbit (w : ClosedWalk) (n : Nat) : w.darts n = orbit (w.darts 0) n :=
  every_reduced_walk_forced w.darts w.step n

def Period (w : ClosedWalk) (p : Nat) : Prop := ∀ n, w.darts (p+n) = w.darts n
theorem period_iff (w : ClosedWalk) (p : Nat) : Period w p ↔ p%3=0 := by
  constructor
  · intro h
    have h0 := h 0
    rw [Nat.add_zero,closed_walk_orbit w p] at h0
    exact (orbit_return_iff (w.darts 0) p).mp h0
  · intro hp n
    rw [closed_walk_orbit w (p+n),closed_walk_orbit w n]
    exact (orbit_period (w.darts 0) p).mpr hp n
theorem length_multiple_three (w : ClosedWalk) : w.length%3=0 :=
  (period_iff w w.length).mp w.periodic

/-- Standard primitivity: a walk is not a repetition of a shorter closed
walk. Periodicity makes each candidate shorter block itself a closed walk. -/
def Primitive (w : ClosedWalk) : Prop :=
  ¬∃ p q : Nat, 0 < p ∧ 2 ≤ q ∧ w.length = p*q ∧ Period w p

theorem primitive_iff_length_three (w : ClosedWalk) : Primitive w ↔ w.length=3 := by
  constructor
  · intro hp
    have hm := length_multiple_three w
    have hpos := w.positive
    by_cases h3 : w.length=3
    · exact h3
    · have hdiv := Nat.mod_add_div w.length 3
      have hq : 2 ≤ w.length/3 := by omega
      have he : w.length = 3*(w.length/3) := by omega
      exact False.elim (hp ⟨3,w.length/3,by decide,hq,he,(period_iff w 3).mpr (by decide)⟩)
  · intro hlen
    rintro ⟨p,q,hp,hq,he,hper⟩
    have hm := (period_iff w p).mp hper
    have hp3 : 3 ≤ p := by omega
    have hprod := Nat.mul_le_mul_left p hq
    rw [← he] at hprod
    omega

def canonical (c : Fin 2) : ClosedWalk where
  length := 3
  positive := by decide
  darts := orbit (if c=0 then 0 else 3)
  step n := (step_is_forced _ _).mpr (orbit_succ _ n)
  periodic := (orbit_period _ 3).mpr (by decide)

abbrev PrimeWalk := {w : ClosedWalk // Primitive w}
def canonicalPrime (c : Fin 2) : PrimeWalk :=
  ⟨canonical c,(primitive_iff_length_three _).mpr rfl⟩
def primeDirection (w : PrimeWalk) : Fin 2 := direction (w.val.darts 0)

def RotationEquivalent (w v : PrimeWalk) : Prop :=
  w.val.length=v.val.length ∧ ∃ s : Nat, ∀ n, w.val.darts (s+n)=v.val.darts n

theorem orbit_reaches_same_direction : ∀ d e : Dart, direction d=direction e →
    ∃ s : Fin 3, orbit d s.val = e := by decide

theorem rotations_iff_direction (w v : PrimeWalk) :
    RotationEquivalent w v ↔ primeDirection w=primeDirection v := by
  constructor
  · rintro ⟨_,s,hs⟩
    have h0 := hs 0
    rw [Nat.add_zero,closed_walk_orbit w.val s] at h0
    exact (orbit_direction (w.val.darts 0) s).symm.trans (congrArg direction h0)
  · intro hd
    obtain ⟨s,hs⟩ := orbit_reaches_same_direction (w.val.darts 0) (v.val.darts 0) hd
    refine ⟨((primitive_iff_length_three _).mp w.property).trans
      ((primitive_iff_length_three _).mp v.property).symm, s.val, ?_⟩
    intro n
    rw [closed_walk_orbit w.val (s.val+n),closed_walk_orbit v.val n,orbit_add,hs]

def rotationSetoid : Setoid PrimeWalk where
  r := RotationEquivalent
  iseqv := ⟨fun w => (rotations_iff_direction w w).mpr rfl,
    fun {w v} h => (rotations_iff_direction v w).mpr ((rotations_iff_direction w v).mp h).symm,
    fun {w v z} h1 h2 => (rotations_iff_direction w z).mpr
      (((rotations_iff_direction w v).mp h1).trans ((rotations_iff_direction v z).mp h2))⟩

/-- Primitive cycles modulo cyclic rotation; reversal is NOT identified. -/
abbrev PrimeCycle := Quotient rotationSetoid
def cycleCode : PrimeCycle → Fin 2 :=
  Quotient.lift primeDirection (fun w v h => (rotations_iff_direction w v).mp h)
def codeCycle (c : Fin 2) : PrimeCycle := Quotient.mk rotationSetoid (canonicalPrime c)

theorem code_after_cycle : ∀ c : Fin 2, cycleCode (codeCycle c) = c := by decide
theorem cycle_after_code (q : PrimeCycle) : codeCycle (cycleCode q) = q := by
  induction q using Quotient.inductionOn with
  | h w =>
    apply Quotient.sound
    apply (rotations_iff_direction _ _).mpr
    exact code_after_cycle (primeDirection w)

def primeLength : PrimeCycle → Nat :=
  Quotient.lift (fun w : PrimeWalk => w.val.length) (fun _ _ h => h.1)
theorem every_prime_length_three (q : PrimeCycle) : primeLength q=3 := by
  induction q using Quotient.inductionOn with
  | h w => exact (primitive_iff_length_three _).mp w.property

def allPrimeCycles : List PrimeCycle := [codeCycle 0,codeCycle 1]
theorem prime_cycles_complete (q : PrimeCycle) : q ∈ allPrimeCycles := by
  have hcode : cycleCode q=0 ∨ cycleCode q=1 := by
    have := (cycleCode q).isLt
    omega
  rw [← cycle_after_code q]
  rcases hcode with h | h <;> simp [allPrimeCycles,h]
theorem prime_cycles_nodup : allPrimeCycles.Nodup := by
  have hne : codeCycle 0 ≠ codeCycle 1 := by
    intro h
    have hh := congrArg cycleCode h
    rw [code_after_cycle,code_after_cycle] at hh
    contradiction
  simp [allPrimeCycles,hne]

/-- Coefficient lists in ascending degree: ordinary integer polynomials.
Multiplication is the full coefficient convolution, and evaluation is Horner. -/
abbrev Polynomial := List Int
def coefficient (p : Polynomial) (n : Nat) : Int := p[n]?.getD 0
def polyAdd (p q : Polynomial) : Polynomial :=
  (List.range (max p.length q.length)).map (fun k => coefficient p k + coefficient q k)
def polyMul (p q : Polynomial) : Polynomial :=
  (List.range (p.length+q.length-1)).map (fun k =>
    ((List.range (k+1)).map (fun i => coefficient p i * coefficient q (k-i))).sum)
def polyPow (p : Polynomial) : Nat → Polynomial
  | 0 => [1]
  | n+1 => polyMul p (polyPow p n)
def evaluate (p : Polynomial) (a : Int) : Int := p.foldr (fun c acc => c+a*acc) 0
def oneMinusPower (n : Nat) : Polynomial :=
  polyAdd [1] ((List.replicate n (0 : Int) ++ [1]).map (fun x => -x))

/-- A rational expression in u with integer-polynomial numerator and
denominator. Products here use genuine polynomial multiplication. -/
structure RationalExpression where
  numerator : Polynomial
  denominator : Polynomial
def ratMultiply (f g : RationalExpression) : RationalExpression :=
  ⟨polyMul f.numerator g.numerator,polyMul f.denominator g.denominator⟩
def eulerFactor (q : PrimeCycle) : RationalExpression := ⟨[1],oneMinusPower (primeLength q)⟩

/-- The defining Ihara Euler product, over ALL primitive oriented cycles
modulo rotation. Completeness and absence of duplicate classes were proved
above, so its finite realization has exactly the standard factors. -/
def iharaZeta : RationalExpression :=
  (allPrimeCycles.map eulerFactor).foldr ratMultiply ⟨[1],[1]⟩

theorem actual_euler_product :
    iharaZeta.numerator=[1] ∧ iharaZeta.denominator=[1,0,0,-2,0,0,1] ∧
    iharaZeta.denominator=polyPow (oneMinusPower 3) 2 := by decide

/-- Algebraic pole order of a rational function at an integer point.
The factorization and both nonzero values assert exact denominator order
and absence of cancellation; this is equivalent to the ordinary complex
meromorphic pole criterion for integer-coefficient rational functions. -/
def HasPoleAt (f : RationalExpression) (a : Int) (order : Nat) : Prop :=
  0 < order ∧ ∃ q : Polynomial,
    f.denominator = polyMul (polyPow [-a,1] order) q ∧
    evaluate q a ≠ 0 ∧ evaluate f.numerator a ≠ 0

def residual : Polynomial := polyPow [1,1,1] 2
theorem pole_at_one_order_two : HasPoleAt iharaZeta 1 2 := by
  exact ⟨by decide,residual,by decide,by decide,by decide⟩
theorem residual_value : evaluate residual 1 = 9 := by decide
theorem numerator_value : evaluate iharaZeta.numerator 1 = 1 := by decide
theorem denominator_not_zero : evaluate iharaZeta.denominator 0 = 1 := by decide

/-- Only these elementary scalar laws are needed to exclude the eigenvalue
one. They hold in R and C (and in every characteristic-not-two field).
They are explicit hypotheses of the theorem, not new axioms. -/
structure ScalarLaws (K : Type) where
  zero : K
  one : K
  add : K → K → K
  mul : K → K → K
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_zero : ∀ x, add x zero = x
  zero_add : ∀ x, add zero x = x
  cancel_left : ∀ x y z, add x y = add x z → y=z
  double_zero : ∀ x, add x x = zero → x=zero
  zero_mul : ∀ x, mul zero x = zero
  one_mul : ∀ x, mul one x = x
  one_ne_zero : one ≠ zero

def adjacencyEntry {K : Type} (S : ScalarLaws K) (i j : Vertex) : K :=
  if adjacent i j then S.one else S.zero
def adjacencyAction {K : Type} (S : ScalarLaws K) (v : Vertex → K) (i : Vertex) : K :=
  ((List.finRange 3).map (fun j => S.mul (adjacencyEntry S i j) (v j))).foldr S.add S.zero

def Eigenvalue {K : Type} (S : ScalarLaws K) (value : K) : Prop :=
  ∃ v : Vertex → K, (∃ i, v i ≠ S.zero) ∧ ∀ i, adjacencyAction S v i = S.mul value (v i)

theorem actual_matrix_rows {K : Type} (S : ScalarLaws K) (v : Vertex → K) :
    adjacencyAction S v 0 = S.add (v 1) (v 2) ∧
    adjacencyAction S v 1 = S.add (v 0) (v 2) ∧
    adjacencyAction S v 2 = S.add (v 0) (v 1) := by
  simp [adjacencyAction,adjacencyEntry,adjacent,List.finRange_succ,List.finRange_zero,
    S.zero_mul,S.one_mul,S.add_zero,S.zero_add]

theorem eigen_equations_force_zero {K : Type} (S : ScalarLaws K) (x y z : K)
    (h0 : x = S.add y z) (h1 : y = S.add x z) (h2 : z = S.add x y) :
    x=S.zero ∧ y=S.zero ∧ z=S.zero := by
  have hh : S.add x (S.add z z) = x := by
    calc
      S.add x (S.add z z) = S.add (S.add x z) z := (S.add_assoc x z z).symm
      _ = S.add y z := congrArg (fun t => S.add t z) h1.symm
      _ = x := h0.symm
  have hz : z=S.zero := S.double_zero z
    (S.cancel_left x (S.add z z) S.zero (hh.trans (S.add_zero x).symm))
  have hxy : x=y := by simpa only [hz,S.add_zero] using h0
  have hxx : S.add x x=S.zero := by simpa only [← hxy,hz] using h2.symm
  have hx := S.double_zero x hxx
  exact ⟨hx,hxy.symm.trans hx,hz⟩

theorem one_not_adjacency_eigenvalue {K : Type} (S : ScalarLaws K) : ¬Eigenvalue S S.one := by
  rintro ⟨v,⟨i,hne⟩,hv⟩
  have hr := actual_matrix_rows S v
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  rw [hr.1,S.one_mul] at h0
  rw [hr.2.1,S.one_mul] at h1
  rw [hr.2.2,S.one_mul] at h2
  obtain ⟨hzero,hOne,hTwo⟩ := eigen_equations_force_zero S (v 0) (v 1) (v 2) h0.symm h1.symm h2.symm
  have hi : i=0 ∨ i=1 ∨ i=2 := by
    have all : ∀ j : Vertex, j=0 ∨ j=1 ∨ j=2 := by decide
    exact all i
  rcases hi with rfl | rfl | rfl
  · exact hne hzero
  · exact hne hOne
  · exact hne hTwo

theorem one_is_its_reciprocal {K : Type} (S : ScalarLaws K) : S.mul S.one S.one = S.one :=
  S.one_mul S.one

/-- A concrete consistent scalar interface; the main result remains generic,
and so excludes arbitrary complex eigenvectors as well as integer vectors. -/
def integerScalars : ScalarLaws Int where
  zero := 0
  one := 1
  add := (·+·)
  mul := (·*·)
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  cancel_left := by intro x y z h; omega
  double_zero := by intro x h; omega
  zero_mul := Int.zero_mul
  one_mul := Int.one_mul
  one_ne_zero := by decide

/-- The source's pole-reciprocal claim implies this necessary instance.
The actual Ihara function has a pole at one, while reciprocal one is not
an eigenvalue of the actual adjacency action on any eligible scalar field. -/
theorem conjecture6542_false {K : Type} (S : ScalarLaws K) :
    ¬(HasPoleAt iharaZeta 1 2 → Eigenvalue S S.one) := by
  intro h
  exact one_not_adjacency_eigenvalue S (h pole_at_one_order_two)

#print axioms fromFiniteWord
#print axioms primitive_iff_length_three
#print axioms rotations_iff_direction
#print axioms prime_cycles_complete
#print axioms prime_cycles_nodup
#print axioms actual_euler_product
#print axioms pole_at_one_order_two
#print axioms one_not_adjacency_eigenvalue
#print axioms conjecture6542_false
end Conjecture6542
