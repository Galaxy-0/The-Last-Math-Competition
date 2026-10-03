import Std

/-! With the problem's definition (torsion-free quotient), a directed union
of pure subgroups is pure. Actual coset quotients and their full group laws
are constructed here, before the quotient criterion is used. -/
namespace Conjecture04287

structure GroupData (A : Type) where
  zero : A
  add : A → A → A
  neg : A → A
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  zero_add : ∀ x, add zero x = x
  add_zero : ∀ x, add x zero = x
  neg_add : ∀ x, add (neg x) x = zero
  add_neg : ∀ x, add x (neg x) = zero

/-- A normal subgroup, as needed for a quotient group. In an abelian
group all subgroups are normal, but no abelian assumption is needed. -/
structure Subgroup {A : Type} (D : GroupData A) where
  carrier : A → Prop
  zero_mem : carrier D.zero
  add_mem : ∀ x y, carrier x → carrier y → carrier (D.add x y)
  neg_mem : ∀ x, carrier x → carrier (D.neg x)
  normal : ∀ g x, carrier x → carrier (D.add g (D.add x (D.neg g)))

def multiples {A : Type} (D : GroupData A) : Nat → A → A
  | 0, _ => D.zero
  | n+1, x => D.add (multiples D n x) x

def TorsionFree {A : Type} (D : GroupData A) : Prop :=
  ∀ n : Nat, 0 < n → ∀ x : A, multiples D n x = D.zero → x = D.zero

theorem add_neg {A : Type} (D : GroupData A) (x : A) :
    D.add x (D.neg x) = D.zero := D.add_neg x

theorem inverse_unique {A : Type} (D : GroupData A) (x y : A)
    (h : D.add x y = D.zero) : x = D.neg y := by
  calc
    x = D.add x D.zero := (D.add_zero x).symm
    _ = D.add x (D.add y (D.neg y)) := congrArg (D.add x) (add_neg D y).symm
    _ = D.add (D.add x y) (D.neg y) := (D.add_assoc _ _ _).symm
    _ = D.add D.zero (D.neg y) := congrArg (fun z => D.add z (D.neg y)) h
    _ = D.neg y := D.zero_add _

theorem neg_neg {A : Type} (D : GroupData A) (x : A) : D.neg (D.neg x) = x :=
  (inverse_unique D x (D.neg x) (D.add_neg x)).symm

theorem add_neg_cancel_left {A : Type} (D : GroupData A) (x y : A) :
    D.add x (D.add (D.neg x) y) = y := by
  rw [← D.add_assoc, D.add_neg, D.zero_add]

theorem neg_add_cancel_left {A : Type} (D : GroupData A) (x y : A) :
    D.add (D.neg x) (D.add x y) = y := by
  rw [← D.add_assoc, D.neg_add, D.zero_add]

theorem neg_add_distrib {A : Type} (D : GroupData A) (x y : A) :
    D.add (D.neg y) (D.neg x) = D.neg (D.add x y) := by
  apply inverse_unique D
  calc
    D.add (D.add (D.neg y) (D.neg x)) (D.add x y) =
        D.add (D.neg y) (D.add (D.neg x) (D.add x y)) := D.add_assoc _ _ _
    _ = D.add (D.neg y) y := congrArg (D.add (D.neg y)) (neg_add_cancel_left D x y)
    _ = D.zero := D.neg_add y

/-- Ordinary additive cosets: x and y differ by an element of H. -/
def CosetRel {A : Type} {D : GroupData A} (H : Subgroup D) (x y : A) : Prop :=
  ∃ h : A, H.carrier h ∧ D.add x h = y

theorem coset_refl {A : Type} {D : GroupData A} (H : Subgroup D) (x : A) :
    CosetRel H x x := ⟨D.zero, H.zero_mem, D.add_zero x⟩

theorem coset_symm {A : Type} {D : GroupData A} (H : Subgroup D)
    {x y : A} (h : CosetRel H x y) : CosetRel H y x := by
  obtain ⟨a, ha, hxy⟩ := h
  refine ⟨D.neg a, H.neg_mem a ha, ?_⟩
  calc
    D.add y (D.neg a) = D.add (D.add x a) (D.neg a) :=
      congrArg (fun z => D.add z (D.neg a)) hxy.symm
    _ = D.add x (D.add a (D.neg a)) := D.add_assoc _ _ _
    _ = D.add x D.zero := congrArg (D.add x) (add_neg D a)
    _ = x := D.add_zero x

theorem coset_trans {A : Type} {D : GroupData A} (H : Subgroup D)
    {x y z : A} (hxy : CosetRel H x y) (hyz : CosetRel H y z) : CosetRel H x z := by
  obtain ⟨a, ha, hxa⟩ := hxy
  obtain ⟨b, hb, hyb⟩ := hyz
  refine ⟨D.add a b, H.add_mem a b ha hb, ?_⟩
  calc
    D.add x (D.add a b) = D.add (D.add x a) b := (D.add_assoc _ _ _).symm
    _ = D.add y b := congrArg (fun t => D.add t b) hxa
    _ = z := hyb

def cosetSetoid {A : Type} {D : GroupData A} (H : Subgroup D) : Setoid A where
  r := CosetRel H
  iseqv := ⟨coset_refl H, coset_symm H, coset_trans H⟩

def QuotientGroup {A : Type} {D : GroupData A} (H : Subgroup D) :=
  Quotient (cosetSetoid H)

def project {A : Type} {D : GroupData A} (H : Subgroup D) (x : A) : QuotientGroup H :=
  Quotient.mk (cosetSetoid H) x

theorem coset_add {A : Type} {D : GroupData A} (H : Subgroup D)
    {x x' y y' : A} (hx : CosetRel H x x') (hy : CosetRel H y y') :
    CosetRel H (D.add x y) (D.add x' y') := by
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨b, hb, hyb⟩ := hy
  have hconj : H.carrier (D.add (D.neg y) (D.add a y)) := by
    have ht := H.normal (D.neg y) a ha
    simpa only [neg_neg] using ht
  refine ⟨D.add (D.add (D.neg y) (D.add a y)) b,
    H.add_mem _ _ hconj hb, ?_⟩
  calc
    D.add (D.add x y) (D.add (D.add (D.neg y) (D.add a y)) b) =
        D.add (D.add x a) (D.add y b) := by
      simp only [D.add_assoc, add_neg_cancel_left]
    _ = D.add x' y' := by rw [hxa, hyb]

theorem coset_neg {A : Type} {D : GroupData A} (H : Subgroup D)
    {x y : A} (hxy : CosetRel H x y) : CosetRel H (D.neg x) (D.neg y) := by
  obtain ⟨a, ha, hxa⟩ := hxy
  refine ⟨D.add x (D.add (D.neg a) (D.neg x)), H.normal x _ (H.neg_mem a ha), ?_⟩
  calc
    D.add (D.neg x) (D.add x (D.add (D.neg a) (D.neg x))) =
        D.add (D.neg a) (D.neg x) := neg_add_cancel_left D x _
    _ = D.neg (D.add x a) := neg_add_distrib D x a
    _ = D.neg y := congrArg D.neg hxa

def quotientAdd {A : Type} {D : GroupData A} (H : Subgroup D)
    (x y : QuotientGroup H) : QuotientGroup H :=
  Quotient.liftOn₂ x y (fun a b => project H (D.add a b))
    (fun _ _ _ _ h1 h2 => Quotient.sound (coset_add H h1 h2))

def quotientNeg {A : Type} {D : GroupData A} (H : Subgroup D)
    (x : QuotientGroup H) : QuotientGroup H :=
  Quotient.liftOn x (fun a => project H (D.neg a))
    (fun _ _ h => Quotient.sound (coset_neg H h))

/-- The actual quotient group, with every group law proved.
No commutativity assumption is made; subgroups here are normal. -/
def quotientStructure {A : Type} {D : GroupData A} (H : Subgroup D) :
    GroupData (QuotientGroup H) where
  zero := project H D.zero
  add := quotientAdd H
  neg := quotientNeg H
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    exact congrArg (project H) (D.add_assoc a b c)
  zero_add := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact congrArg (project H) (D.zero_add a)
  add_zero := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact congrArg (project H) (D.add_zero a)
  neg_add := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact congrArg (project H) (D.neg_add a)
  add_neg := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact congrArg (project H) (D.add_neg a)

theorem project_zero_iff {A : Type} {D : GroupData A} (H : Subgroup D) (x : A) :
    project H x = project H D.zero ↔ H.carrier x := by
  constructor
  · intro h
    obtain ⟨a, ha, hxa⟩ := Quotient.exact h
    have hx : x = D.neg a := inverse_unique D x a hxa
    rw [hx]
    exact H.neg_mem a ha
  · intro hx
    exact Quotient.sound ⟨D.neg x, H.neg_mem x hx, add_neg D x⟩

theorem project_multiples {A : Type} {D : GroupData A} (H : Subgroup D)
    (n : Nat) (x : A) :
    multiples (quotientStructure H) n (project H x) = project H (multiples D n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change quotientAdd H (multiples (quotientStructure H) n (project H x)) (project H x) = _
    rw [ih]
    rfl

/-- This is the definition in the problem: the quotient is torsion-free. -/
def Pure {A : Type} {D : GroupData A} (H : Subgroup D) : Prop :=
  TorsionFree (quotientStructure H)

def RootClosed {A : Type} {D : GroupData A} (H : Subgroup D) : Prop :=
  ∀ n : Nat, 0 < n → ∀ x : A, H.carrier (multiples D n x) → H.carrier x

/-- The root-closed criterion is derived from the actual quotient definition. -/
theorem pure_iff_rootClosed {A : Type} {D : GroupData A} (H : Subgroup D) :
    Pure H ↔ RootClosed H := by
  constructor
  · intro hp n hn x hx
    apply (project_zero_iff H x).mp
    apply hp n hn (project H x)
    rw [project_multiples]
    exact (project_zero_iff H (multiples D n x)).mpr hx
  · intro hr n hn q
    refine Quotient.inductionOn q ?_
    intro x hx
    apply (project_zero_iff H x).mpr
    apply hr n hn x
    apply (project_zero_iff H (multiples D n x)).mp
    rw [← project_multiples]
    exact hx

def Included {A : Type} {D : GroupData A} (H K : Subgroup D) : Prop :=
  ∀ x, H.carrier x → K.carrier x

def Directed {A I : Type} {D : GroupData A} (H : I → Subgroup D) : Prop :=
  ∀ i j, ∃ k, Included (H i) (H k) ∧ Included (H j) (H k)

def Chain {A I : Type} {D : GroupData A} (H : I → Subgroup D) : Prop :=
  ∀ i j, Included (H i) (H j) ∨ Included (H j) (H i)

theorem chain_directed {A I : Type} {D : GroupData A} {H : I → Subgroup D}
    (hc : Chain H) : Directed H := by
  intro i j
  rcases hc i j with h | h
  · exact ⟨j, h, fun _ hx => hx⟩
  · exact ⟨i, (fun _ hx => hx), h⟩

def unionSubgroup {A I : Type} {D : GroupData A}
    (H : I → Subgroup D) (hI : Nonempty I) (hd : Directed H) : Subgroup D where
  carrier x := ∃ i, (H i).carrier x
  zero_mem := by
    obtain ⟨i⟩ := hI
    exact ⟨i, (H i).zero_mem⟩
  add_mem x y hx hy := by
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, (H k).add_mem x y (hik x hi) (hjk y hj)⟩
  neg_mem x hx := by
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, (H i).neg_mem x hi⟩
  normal g x hx := by
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, (H i).normal g x hi⟩

theorem directed_union_pure {A I : Type} {D : GroupData A}
    (H : I → Subgroup D) (hI : Nonempty I) (hd : Directed H)
    (hp : ∀ i, Pure (H i)) : Pure (unionSubgroup H hI hd) := by
  apply (pure_iff_rootClosed _).mpr
  intro n hn x hx
  obtain ⟨i, hi⟩ := hx
  exact ⟨i, ((pure_iff_rootClosed (H i)).mp (hp i)) n hn x hi⟩

theorem arbitrary_chain_union_pure {A I : Type} {D : GroupData A}
    (H : I → Subgroup D) (hI : Nonempty I) (hc : Chain H)
    (hp : ∀ i, Pure (H i)) : Pure (unionSubgroup H hI (chain_directed hc)) :=
  directed_union_pure H hI (chain_directed hc) hp

/-- Forgetting the length of a putative transfinite counterexample leaves
a nonempty chain of pure subgroups whose union is not pure. -/
def BadChainExists {A : Type} (D : GroupData A) : Prop :=
  ∃ (I : Type) (H : I → Subgroup D) (hI : Nonempty I) (hc : Chain H),
    (∀ i, Pure (H i)) ∧ ¬ Pure (unionSubgroup H hI (chain_directed hc))

theorem no_bad_chain {A : Type} (D : GroupData A) : ¬ BadChainExists D := by
  rintro ⟨I, H, hI, hc, hp, hbad⟩
  exact hbad (arbitrary_chain_union_pure H hI hc hp)

/-- A necessary consequence of the assertion that counterexamples exist
at every chain length beyond omega. -/
def ClaimedFailureExists : Prop :=
  ∃ (A : Type) (D : GroupData A), BadChainExists D

theorem conjecture04287_false : ¬ ClaimedFailureExists := by
  rintro ⟨A, D, hbad⟩
  exact no_bad_chain D hbad

theorem full_conjecture_false (OtherAssertions : Prop) :
    ¬ (ClaimedFailureExists ∧ OtherAssertions) := by
  intro h
  exact conjecture04287_false h.1

#print axioms quotientStructure
#print axioms project_zero_iff
#print axioms project_multiples
#print axioms pure_iff_rootClosed
#print axioms directed_union_pure
#print axioms arbitrary_chain_union_pure
#print axioms conjecture04287_false
#print axioms full_conjecture_false
end Conjecture04287
