import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Conjecture1184

/-- Entries are residues modulo 5, represented by natural numbers from 0 to 4. -/
abbrev Matrix := Nat × Nat × Nat × Nat

def neg (x : Nat) : Nat := (5 - x % 5) % 5

/-- Pick the sign whose first nonzero entry in the first row is 1 or 2. -/
def normalize (x : Matrix) : Matrix :=
  let (a,b,c,d) := x
  if a > 2 ∨ (a = 0 ∧ b > 2) then (neg a, neg b, neg c, neg d) else x

/-- Matrix product in SL₂(F₅), followed by quotienting by {I,-I}. -/
def mul (x y : Matrix) : Matrix :=
  let (a,b,c,d) := x
  let (e,f,g,h) := y
  normalize ((a*e+b*g)%5, (a*f+b*h)%5, (c*e+d*g)%5, (c*f+d*h)%5)

def one : Matrix := (1,0,0,1)
def inv (x : Matrix) : Matrix :=
  let (a,b,c,d) := x
  normalize (d,neg b,neg c,a)

def decode (n : Nat) : Matrix := (n/125, n/25%5, n/5%5, n%5)

def isCanonicalSL (x : Matrix) : Bool :=
  let (a,b,c,d) := x
  decide ((a*d+5-(b*c)%5)%5 = 1 ∧ (a = 1 ∨ a = 2 ∨ (a = 0 ∧ (b = 1 ∨ b = 2))))

/-- The canonical representatives of PSL₂(F₅) = SL₂(F₅)/{I,-I}. -/
def groupElements : List Matrix := ((List.range 625).map decode).filter isCanonicalSL

/-- Explicit enumeration, checked against the field-arithmetic definition. -/
def reps : List Matrix := [(0, 1, 4, 0), (0, 1, 4, 1), (0, 1, 4, 2), (0, 1, 4, 3), (0, 1, 4, 4), (0, 2, 2, 0), (0, 2, 2, 1), (0, 2, 2, 2), (0, 2, 2, 3), (0, 2, 2, 4), (1, 0, 0, 1), (1, 0, 1, 1), (1, 0, 2, 1), (1, 0, 3, 1), (1, 0, 4, 1), (1, 1, 0, 1), (1, 1, 1, 2), (1, 1, 2, 3), (1, 1, 3, 4), (1, 1, 4, 0), (1, 2, 0, 1), (1, 2, 1, 3), (1, 2, 2, 0), (1, 2, 3, 2), (1, 2, 4, 4), (1, 3, 0, 1), (1, 3, 1, 4), (1, 3, 2, 2), (1, 3, 3, 0), (1, 3, 4, 3), (1, 4, 0, 1), (1, 4, 1, 0), (1, 4, 2, 4), (1, 4, 3, 3), (1, 4, 4, 2), (2, 0, 0, 3), (2, 0, 1, 3), (2, 0, 2, 3), (2, 0, 3, 3), (2, 0, 4, 3), (2, 1, 0, 3), (2, 1, 1, 1), (2, 1, 2, 4), (2, 1, 3, 2), (2, 1, 4, 0), (2, 2, 0, 3), (2, 2, 1, 4), (2, 2, 2, 0), (2, 2, 3, 1), (2, 2, 4, 2), (2, 3, 0, 3), (2, 3, 1, 2), (2, 3, 2, 1), (2, 3, 3, 0), (2, 3, 4, 4), (2, 4, 0, 3), (2, 4, 1, 0), (2, 4, 2, 2), (2, 4, 3, 4), (2, 4, 4, 1)]

theorem enumeration_correct : groupElements = reps := by decide
theorem group_order : groupElements.length = 60 := by
  rw [enumeration_correct]
  decide

def subgroups : List (List Matrix) := [
  [(0, 1, 4, 0), (0, 2, 2, 0), (1, 0, 0, 1), (1, 1, 2, 3), (1, 2, 1, 3), (1, 3, 4, 3), (1, 4, 3, 3), (2, 0, 0, 3), (2, 1, 2, 4), (2, 2, 1, 4), (2, 3, 4, 4), (2, 4, 3, 4)],
  [(0, 1, 4, 1), (0, 2, 2, 1), (1, 0, 0, 1), (1, 1, 2, 3), (1, 2, 4, 4), (1, 3, 3, 0), (1, 4, 1, 0), (2, 0, 3, 3), (2, 1, 2, 4), (2, 2, 4, 2), (2, 3, 1, 2), (2, 4, 0, 3)],
  [(0, 1, 4, 1), (0, 2, 2, 4), (1, 0, 0, 1), (1, 1, 3, 4), (1, 2, 2, 0), (1, 3, 4, 3), (1, 4, 1, 0), (2, 0, 1, 3), (2, 1, 3, 2), (2, 2, 0, 3), (2, 3, 4, 4), (2, 4, 2, 2)],
  [(0, 1, 4, 4), (0, 2, 2, 1), (1, 0, 0, 1), (1, 1, 4, 0), (1, 2, 1, 3), (1, 3, 3, 0), (1, 4, 2, 4), (2, 0, 4, 3), (2, 1, 3, 2), (2, 2, 1, 4), (2, 3, 0, 3), (2, 4, 2, 2)],
  [(0, 1, 4, 4), (0, 2, 2, 4), (1, 0, 0, 1), (1, 1, 4, 0), (1, 2, 2, 0), (1, 3, 1, 4), (1, 4, 3, 3), (2, 0, 2, 3), (2, 1, 0, 3), (2, 2, 4, 2), (2, 3, 1, 2), (2, 4, 3, 4)],
  [(0, 1, 4, 0), (0, 2, 2, 2), (1, 0, 0, 1), (1, 1, 1, 2), (1, 2, 4, 4), (1, 4, 2, 4), (2, 0, 2, 3), (2, 2, 0, 3), (2, 3, 3, 0), (2, 4, 4, 1)],
  [(0, 1, 4, 0), (0, 2, 2, 3), (1, 0, 0, 1), (1, 1, 3, 4), (1, 3, 1, 4), (1, 4, 4, 2), (2, 0, 3, 3), (2, 1, 1, 1), (2, 2, 2, 0), (2, 3, 0, 3)],
  [(0, 1, 4, 2), (0, 2, 2, 0), (1, 0, 0, 1), (1, 1, 3, 4), (1, 2, 4, 4), (1, 3, 2, 2), (2, 0, 4, 3), (2, 1, 0, 3), (2, 2, 3, 1), (2, 4, 1, 0)]
]

def subgroupCheck (s : List Matrix) : Bool :=
  s.contains one && s.all (fun x => s.contains (inv x) && s.all (fun y => s.contains (mul x y)))

def witness : Matrix := (0, 1, 4, 3)

def certificateCheck : Bool := subgroups.all (fun s => subgroupCheck s && !s.contains witness)

theorem subgroup_certificates : certificateCheck = true := by decide

theorem witness_mem : witness ∈ groupElements := by
  rw [enumeration_correct]
  decide



def determinantOne (x : Matrix) : Bool :=
  let (a,b,c,d) := x
  (a*d+5-(b*c)%5)%5 == 1

def slElements : List Matrix := ((List.range 625).map decode).filter determinantOne

def negMatrix (x : Matrix) : Matrix :=
  let (a,b,c,d) := x
  (neg a,neg b,neg c,neg d)

def rawMul (x y : Matrix) : Matrix :=
  let (a,b,c,d) := x
  let (e,f,g,h) := y
  ((a*e+b*g)%5, (a*f+b*h)%5, (c*e+d*g)%5, (c*f+d*h)%5)

def rawInv (x : Matrix) : Matrix :=
  let (a,b,c,d) := x
  (d,neg b,neg c,a)

theorem sl_order : slElements.length = 120 := by decide
theorem sl_nodup : slElements.Nodup := by decide

def quotientCheck : Bool := slElements.all (fun x =>
  reps.contains (normalize x) &&
  (normalize (rawInv x) == inv (normalize x)) &&
  slElements.all (fun y =>
    decide ((normalize x = normalize y) ↔ (x = y ∨ x = negMatrix y)) &&
    (normalize (rawMul x y) == mul (normalize x) (normalize y))))

theorem canonical_representatives_certificate :
    reps.all (fun x => slElements.contains x && (normalize x == x)) = true := by decide

theorem canonical_representatives {x : Matrix} (hx : x ∈ groupElements) :
    x ∈ slElements ∧ normalize x = x := by
  rw [enumeration_correct] at hx
  have h := List.all_eq_true.mp canonical_representatives_certificate x hx
  simpa only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] using h

theorem quotient_certificate : quotientCheck = true := by decide

/-- The canonicalization fibers are exactly the pairs {M,-M}. -/
theorem normalize_fibers {x y : Matrix} (hx : x ∈ slElements) (hy : y ∈ slElements) :
    normalize x = normalize y ↔ x = y ∨ x = negMatrix y := by
  have h := List.all_eq_true.mp quotient_certificate x hx
  simp only [Bool.and_eq_true] at h
  have hxy := List.all_eq_true.mp h.2 y hy
  simp only [Bool.and_eq_true] at hxy
  exact of_decide_eq_true hxy.1

/-- Matrix multiplication descends to the canonical representatives. -/
theorem normalize_product {x y : Matrix} (hx : x ∈ slElements) (hy : y ∈ slElements) :
    normalize (rawMul x y) = mul (normalize x) (normalize y) := by
  have h := List.all_eq_true.mp quotient_certificate x hx
  simp only [Bool.and_eq_true] at h
  have hxy := List.all_eq_true.mp h.2 y hy
  simp only [Bool.and_eq_true] at hxy
  exact eq_of_beq hxy.2


private theorem mod_left (a b c d : Nat) :
    (a % 5 * b + c % 5 * d) % 5 = (a*b+c*d)%5 := by
  rw [Nat.add_mod, Nat.mod_mul_mod, Nat.mod_mul_mod, ← Nat.add_mod]
private theorem mod_right (a b c d : Nat) :
    (a * (b % 5) + c * (d % 5)) % 5 = (a*b+c*d)%5 := by
  rw [Nat.add_mod, Nat.mul_mod_mod, Nat.mul_mod_mod, ← Nat.add_mod]
theorem rawMul_assoc (x y z : Matrix) : rawMul (rawMul x y) z = rawMul x (rawMul y z) := by
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨e,f,g,h⟩
  rcases z with ⟨i,j,k,l⟩
  simp only [rawMul, mod_left, mod_right]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  ac_rfl

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rawClosureCheck : Bool := reps.all (fun x => reps.all (fun y => slElements.contains (rawMul x y)))
theorem raw_closure_certificate : rawClosureCheck = true := by decide

theorem raw_mul_mem {x y : Matrix} (hx : x ∈ groupElements) (hy : y ∈ groupElements) :
    rawMul x y ∈ slElements := by
  rw [enumeration_correct] at hx hy
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp (List.all_eq_true.mp raw_closure_certificate x hx) y hy)

theorem mul_assoc {x y z : Matrix} (hx : x ∈ groupElements)
    (hy : y ∈ groupElements) (hz : z ∈ groupElements) :
    mul (mul x y) z = mul x (mul y z) := by
  have ⟨hxsl, hxn⟩ := canonical_representatives hx
  have ⟨hysl, hyn⟩ := canonical_representatives hy
  have ⟨hzsl, hzn⟩ := canonical_representatives hz
  have hl := normalize_product (raw_mul_mem hx hy) hzsl
  have hr := normalize_product hxsl (raw_mul_mem hy hz)
  rw [hzn] at hl
  rw [hxn] at hr
  change normalize (rawMul (rawMul x y) z) = mul (mul x y) z at hl
  change normalize (rawMul x (rawMul y z)) = mul x (mul y z) at hr
  rw [← hl, ← hr, rawMul_assoc]


theorem groupElements_nodup : groupElements.Nodup := by
  rw [enumeration_correct]
  decide

theorem subgroup_sizes : subgroups.map List.length = [12,12,12,12,12,10,10,10] := by decide

theorem subgroup_nodup_certificate : subgroups.all (fun s => decide s.Nodup) = true := by decide

theorem subgroups_nodup {s : List Matrix} (hs : s ∈ subgroups) : s.Nodup := by
  exact of_decide_eq_true (List.all_eq_true.mp subgroup_nodup_certificate s hs)

def subgroupMembershipCheck : Bool := subgroups.all (fun s => s.all (fun x => reps.contains x))
theorem subgroup_membership_certificate : subgroupMembershipCheck = true := by decide

theorem subgroups_are_subsets {s : List Matrix} (hs : s ∈ subgroups) : s ⊆ groupElements := by
  intro x hx
  rw [enumeration_correct]
  have h := List.all_eq_true.mp subgroup_membership_certificate s hs
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h x hx)


theorem mul_mem {x y : Matrix} (hx : x ∈ groupElements) (hy : y ∈ groupElements) :
    mul x y ∈ groupElements := by
  rw [enumeration_correct]
  have h := List.all_eq_true.mp quotient_certificate (rawMul x y) (raw_mul_mem hx hy)
  simp only [Bool.and_eq_true] at h
  exact List.contains_iff_mem.mp h.1.1

def elementaryGroupCheck : Bool := reps.all (fun x =>
  reps.contains (inv x) && (mul one x == x) && (mul x one == x) &&
  (mul x (inv x) == one) && (mul (inv x) x == one))

theorem elementary_group_certificate : elementaryGroupCheck = true := by decide

/-- Closure, identity, inverses, and associativity on the actual PSL₂(F₅) model. -/
theorem matrix_group_axioms :
    one ∈ groupElements ∧ ∀ x ∈ groupElements,
      inv x ∈ groupElements ∧ mul one x = x ∧ mul x one = x ∧
      mul x (inv x) = one ∧ mul (inv x) x = one ∧
      ∀ y ∈ groupElements, mul x y ∈ groupElements ∧
        ∀ z ∈ groupElements, mul (mul x y) z = mul x (mul y z) := by
  constructor
  · rw [enumeration_correct]; decide
  · intro x hx
    have hxrep : x ∈ reps := by simpa [enumeration_correct] using hx
    have h := List.all_eq_true.mp elementary_group_certificate x hxrep
    simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq, and_assoc] at h
    obtain ⟨hi, hl, hr, hri, hli⟩ := h
    rw [← enumeration_correct] at hi
    exact ⟨hi, hl, hr, hri, hli, fun y hy => ⟨mul_mem hx hy, fun z hz => mul_assoc hx hy hz⟩⟩

/-- The subgroup generated by two matrices, using exactly group words. -/
inductive Generated (a b : Matrix) : Matrix → Prop
  | unit : Generated a b one
  | left : Generated a b a
  | right : Generated a b b
  | product {x y} : Generated a b x → Generated a b y → Generated a b (mul x y)
  | inverse {x} : Generated a b x → Generated a b (inv x)

def Generates (a b : Matrix) : Prop := ∀ x ∈ groupElements, Generated a b x

theorem certificate_properties {s : List Matrix} (hs : s ∈ subgroups) :
    one ∈ s ∧ (∀ x ∈ s, inv x ∈ s ∧ ∀ y ∈ s, mul x y ∈ s) ∧ witness ∉ s := by
  have h := (List.all_eq_true.mp subgroup_certificates) s hs
  simpa [certificateCheck, subgroupCheck, Bool.and_eq_true,
    List.all_eq_true, List.contains_iff_mem, and_assoc] using h

theorem generated_stays {a b x : Matrix} {s : List Matrix}
    (hs : s ∈ subgroups) (ha : a ∈ s) (hb : b ∈ s) (hx : Generated a b x) : x ∈ s := by
  obtain ⟨hunit, hclosed, _⟩ := certificate_properties hs
  induction hx with
  | unit => exact hunit
  | left => exact ha
  | right => exact hb
  | product hx hy ihx ihy => exact (hclosed _ ihx).2 _ ihy
  | inverse hx ih => exact (hclosed _ ih).1

theorem shared_subgroup_not_generating {a b : Matrix} {s : List Matrix}
    (hs : s ∈ subgroups) (ha : a ∈ s) (hb : b ∈ s) : ¬ Generates a b := by
  intro h
  exact (certificate_properties hs).2.2 (generated_stays hs ha hb (h witness witness_mem))

/-- These are the ordered pairs not ruled out by the eight certificates. -/
def possible (p : Matrix × Matrix) : Bool :=
  subgroups.all (fun s => !(s.contains p.1 && s.contains p.2))

theorem generating_is_possible {a b : Matrix} (h : Generates a b) :
    possible (a,b) = true := by
  apply List.all_eq_true.mpr
  intro s hs
  have hn := shared_subgroup_not_generating (a := a) (b := b) hs
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff]
  by_cases ha : a ∈ s
  · right
    apply Bool.eq_false_iff.mpr
    intro hb
    exact hn ha (List.contains_iff_mem.mp hb) h
  · left
    apply Bool.eq_false_iff.mpr
    intro hh
    exact ha (List.contains_iff_mem.mp hh)

def orderedPairs : List (Matrix × Matrix) :=
  groupElements.flatMap (fun a => groupElements.map (fun b => (a,b)))

def possibleCount : Nat := (orderedPairs.filter possible).length

theorem possible_count : possibleCount = 2712 := by
  unfold possibleCount orderedPairs
  rw [enumeration_correct]
  decide

noncomputable def generatingCount : Nat := by
  classical
  exact (orderedPairs.filter (fun p => decide (Generates p.1 p.2))).length

/-- Pointwise implication bounds the numbers selected from a finite list. -/
theorem filter_count_mono {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x
    · simpa [hp, hq] using ih
    · simp [hp, hq]
      omega
    · have hh := h x hp
      simp [hq] at hh
    · simpa [hp, hq] using ih

theorem generating_count_bound : generatingCount ≤ 2712 := by
  classical
  have h := filter_count_mono orderedPairs
    (fun p => decide (Generates p.1 p.2)) possible
    (by intro p hp; exact generating_is_possible (of_decide_eq_true hp))
  change generatingCount ≤ possibleCount at h
  simpa [possible_count] using h

/-- For q = 5, the conjectured probability bound is P ≥ 19/25. -/
def ClaimedDixonBoundAtFive : Prop :=
  19 * (groupElements.length * groupElements.length) ≤ 25 * generatingCount

/-- The asserted finite Lie-type lower bound fails for PSL₂(F₅). -/
theorem conjecture1184_false : ¬ ClaimedDixonBoundAtFive := by
  unfold ClaimedDixonBoundAtFive
  rw [group_order]
  have h := generating_count_bound
  omega



theorem orderedPairs_nodup : orderedPairs.Nodup := by
  unfold orderedPairs List.Nodup
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a ha
    apply List.pairwise_map.mpr
    exact groupElements_nodup.imp (by intro x y hne heq; exact hne (congrArg Prod.snd heq))
  · apply groupElements_nodup.imp
    intro a b hab x hx y hy heq
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
    exact hab (congrArg Prod.fst heq)


#print axioms conjecture1184_false
#print axioms matrix_group_axioms
#print axioms normalize_fibers
#print axioms normalize_product
end Conjecture1184
