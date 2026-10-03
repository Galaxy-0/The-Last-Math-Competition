import Std

/-! A symmetric-difference-closed family with exactly three atoms.
All subsets are genuine Prop-valued subsets of Fin 3. The eight-element
family enumeration and the three-element atom enumeration are both proved
complete and duplicate-free. -/
namespace Conjecture06402

abbrev Point := Fin 3
abbrev Subset := Point → Prop
abbrev Family := Subset → Prop

def Included (S T : Subset) : Prop := ∀ x, S x → T x
def NonemptySet (S : Subset) : Prop := ∃ x, S x
def symDiff (S T : Subset) : Subset := fun x => (S x ∧ ¬T x) ∨ (T x ∧ ¬S x)
def DifferenceClosed (F : Family) : Prop := ∀ S T, F S → F T → F (symDiff S T)

def IsAtom (F : Family) (S : Subset) : Prop :=
  F S ∧ NonemptySet S ∧
    ∀ T : Subset, F T → Included T S → NonemptySet T → T = S

abbrev Atom (F : Family) := {S : Subset // IsAtom F S}

def fullFamily : Family := fun _ => True

theorem fullFamily_closed : DifferenceClosed fullFamily := fun _ _ _ _ => True.intro

def singleton (i : Point) : Subset := fun x => x = i

theorem singleton_is_atom (i : Point) : IsAtom fullFamily (singleton i) := by
  refine ⟨True.intro, ⟨i, rfl⟩, ?_⟩
  intro T _ hT hne
  obtain ⟨x, hx⟩ := hne
  have hxi : x = i := hT x hx
  have hi : T i := hxi ▸ hx
  funext y
  apply propext
  constructor
  · exact hT y
  · intro hy
    change y = i at hy
    rw [hy]
    exact hi

def singletonAtom (i : Point) : Atom fullFamily := ⟨singleton i, singleton_is_atom i⟩

/-- Completeness for arbitrary subset predicates, with no finite encoding
assumption: every minimal nonempty subset is an actual singleton. -/
theorem every_atom_is_singleton (a : Atom fullFamily) :
    ∃ i : Point, singletonAtom i = a := by
  obtain ⟨i, hi⟩ := a.property.2.1
  have hs : singleton i = a.val := a.property.2.2 (singleton i) True.intro
    (by intro x hx; change x = i at hx; rw [hx]; exact hi) ⟨i, rfl⟩
  exact ⟨i, Subtype.ext hs⟩

theorem singletonAtom_injective (i j : Point) (h : singletonAtom i = singletonAtom j) :
    i = j := by
  have he := congrArg (fun a : Atom fullFamily => a.val i) h
  change (i = i) = (i = j) at he
  exact Eq.mp he rfl

def atoms : List (Atom fullFamily) := (List.finRange 3).map singletonAtom

theorem atoms_complete (a : Atom fullFamily) : a ∈ atoms := by
  obtain ⟨i, hi⟩ := every_atom_is_singleton a
  apply List.mem_map.mpr
  exact ⟨i, (by decide : ∀ i : Point, i ∈ List.finRange 3) i, hi⟩

theorem atoms_nodup : atoms.Nodup := by
  unfold atoms List.Nodup
  apply List.Pairwise.map singletonAtom ?_
    (by decide : List.Pairwise (fun i j : Point => i ≠ j) (List.finRange 3))
  intro i j hij h
  exact hij (singletonAtom_injective i j h)

theorem atoms_length : atoms.length = 3 := by
  simp only [atoms, List.length_map, List.length_finRange]

/-- Explicit encoding of the entire family establishes its finiteness and
distinguishes the eight members from the three atoms. -/
def decode (m : Fin 8) (x : Point) : Prop := (m.val / 2^x.val) % 2 = 1

noncomputable def encode (S : Subset) : Fin 8 := by
  classical
  exact ⟨((if S 0 then 1 else 0) + (if S 1 then 2 else 0) +
    (if S 2 then 4 else 0)) % 8, Nat.mod_lt _ (by decide)⟩

theorem decode_encode (S : Subset) : decode (encode S) = S := by
  classical
  funext x
  apply propext
  have hc : ∀ x : Point, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hc x with rfl | rfl | rfl <;>
    by_cases h0 : S 0 <;> by_cases h1 : S 1 <;> by_cases h2 : S 2 <;>
    simp [decode, encode, h0, h1, h2] <;> decide

theorem decode_injective (a b : Fin 8) (h : decode a = decode b) : a = b := by
  have checked : ∀ a b : Fin 8,
      (∀ x : Point, decode a x ↔ decode b x) → a = b := by
    unfold decode
    decide
  apply checked a b
  intro x
  exact Iff.of_eq (congrArg (fun S : Subset => S x) h)

def members : List Subset := (List.finRange 8).map decode

theorem members_complete (S : Subset) : S ∈ members := by
  apply List.mem_map.mpr
  exact ⟨encode S, (by decide : ∀ i : Fin 8, i ∈ List.finRange 8) (encode S), decode_encode S⟩

theorem members_nodup : members.Nodup := by
  unfold members List.Nodup
  apply List.Pairwise.map decode ?_
    (by decide : List.Pairwise (fun i j : Fin 8 => i ≠ j) (List.finRange 8))
  intro i j hij h
  exact hij (decode_injective i j h)

theorem members_length : members.length = 8 := by
  simp only [members, List.length_map, List.length_finRange]

def FiniteFamily (F : Family) : Prop :=
  ∃ enumeration : List Subset, enumeration.Nodup ∧ ∀ S, F S ↔ S ∈ enumeration

theorem fullFamily_finite : FiniteFamily fullFamily := by
  refine ⟨members, members_nodup, ?_⟩
  intro S
  exact ⟨fun _ => members_complete S, fun _ => True.intro⟩

theorem three_not_power_of_two (n : Nat) : 3 ≠ 2^n := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      intro h
      have hp : 2^(n+2) = 2^n * 4 := by rw [Nat.pow_add]
      change 3 = 2^(n+2) at h
      rw [hp] at h
      omega

/-- The necessary atom-count claim, already restricted to finite families
on a three-point universe. Count is a complete, duplicate-free enumeration
of actual atoms, not an independently assigned numerical invariant. -/
def ClaimedAtomPower : Prop :=
  ∀ F : Family, FiniteFamily F → DifferenceClosed F →
    ∀ enumeration : List (Atom F), enumeration.Nodup →
      (∀ a : Atom F, a ∈ enumeration) → ∃ n : Nat, enumeration.length = 2^n

theorem conjecture06402_false : ¬ ClaimedAtomPower := by
  intro h
  obtain ⟨n, hn⟩ := h fullFamily fullFamily_finite fullFamily_closed atoms atoms_nodup atoms_complete
  rw [atoms_length] at hn
  exact three_not_power_of_two n hn

theorem full_conjecture_false (OtherAssertions : Prop) :
    ¬ (ClaimedAtomPower ∧ OtherAssertions) := by
  intro h
  exact conjecture06402_false h.1

#print axioms every_atom_is_singleton
#print axioms atoms_complete
#print axioms atoms_nodup
#print axioms decode_encode
#print axioms fullFamily_finite
#print axioms conjecture06402_false
#print axioms full_conjecture_false
end Conjecture06402
