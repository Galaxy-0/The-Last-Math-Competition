import Std

namespace Conjecture6825
universe u v

abbrev Subset (X : Type u) := X → Prop

/-- The usual closed-set axioms for a topology. The intersection is over
all members of an arbitrary predicate-valued family, including the empty one. -/
structure ClosedTopology (X : Type u) where
  closed : Subset X → Prop
  empty_closed : closed (fun _ => False)
  univ_closed : closed (fun _ => True)
  union_closed : ∀ S T, closed S → closed T → closed (fun x => S x ∨ T x)
  intersection_closed : ∀ F : Subset X → Prop,
    (∀ S, F S → closed S) → closed (fun x => ∀ S, F S → S x)

/-- Only closure under the actual vector operations is needed in the proof.
Every real or complex vector space supplies these operations. No extra law
is assumed: the result holds even for arbitrary operations of these arities. -/
structure LinearOperations (K : Type v) (X : Type u) where
  zero : X
  add : X → X → X
  smul : K → X → X

structure InvariantSubspace {K : Type v} {X : Type u}
    (T : ClosedTopology X) (O : LinearOperations K X) (A : X → X) where
  carrier : Subset X
  isClosed : T.closed carrier
  zero_mem : carrier O.zero
  add_mem : ∀ x y, carrier x → carrier y → carrier (O.add x y)
  smul_mem : ∀ a x, carrier x → carrier (O.smul a x)
  invariant : ∀ x, carrier x → carrier (A x)

variable {K : Type v} {X : Type u}
variable {T : ClosedTopology X} {O : LinearOperations K X} {A : X → X}

theorem subspace_ext (U V : InvariantSubspace T O A)
    (h : ∀ x, U.carrier x ↔ V.carrier x) : U = V := by
  have hc : U.carrier = V.carrier := funext (fun x => propext (h x))
  cases U
  cases V
  cases hc
  rfl

/-- The standard order, actual inclusion of the underlying subsets. -/
def Included (U V : InvariantSubspace T O A) : Prop :=
  ∀ x, U.carrier x → V.carrier x

theorem included_refl (U : InvariantSubspace T O A) : Included U U :=
  fun _ h => h
theorem included_trans (U V W : InvariantSubspace T O A)
    (hUV : Included U V) (hVW : Included V W) : Included U W :=
  fun x hx => hVW x (hUV x hx)
theorem included_antisymm (U V : InvariantSubspace T O A)
    (hUV : Included U V) (hVU : Included V U) : U = V :=
  subspace_ext U V (fun x => ⟨hUV x, hVU x⟩)

def whole : InvariantSubspace T O A where
  carrier := fun _ => True
  isClosed := T.univ_closed
  zero_mem := True.intro
  add_mem := fun _ _ _ _ => True.intro
  smul_mem := fun _ _ _ => True.intro
  invariant := fun _ _ => True.intro

def intersection (F : InvariantSubspace T O A → Prop) : InvariantSubspace T O A where
  carrier := fun x => ∀ W, F W → W.carrier x
  isClosed := by
    let G : Subset X → Prop := fun S => ∃ W, F W ∧ W.carrier = S
    have hG : ∀ S, G S → T.closed S := by
      intro S h
      obtain ⟨W, _, he⟩ := h
      rw [← he]
      exact W.isClosed
    have he : (fun x => ∀ W, F W → W.carrier x) =
        (fun x => ∀ S, G S → S x) := by
      funext x
      apply propext
      constructor
      · intro hx S hS
        obtain ⟨W, hW, he⟩ := hS
        rw [← he]
        exact hx W hW
      · intro hx W hW
        exact hx W.carrier ⟨W, hW, rfl⟩
    rw [he]
    exact T.intersection_closed G hG
  zero_mem := fun W _ => W.zero_mem
  add_mem := fun x y hx hy W hW => W.add_mem x y (hx W hW) (hy W hW)
  smul_mem := fun a x hx W hW => W.smul_mem a x (hx W hW)
  invariant := fun x hx W hW => W.invariant x (hx W hW)

theorem intersection_member (F : InvariantSubspace T O A → Prop) (x : X) :
    (intersection F).carrier x ↔ ∀ W, F W → W.carrier x := Iff.rfl

theorem intersection_lower (F : InvariantSubspace T O A → Prop)
    (W : InvariantSubspace T O A) (hW : F W) : Included (intersection F) W :=
  fun _ hx => hx W hW

theorem intersection_greatest (F : InvariantSubspace T O A → Prop)
    (L : InvariantSubspace T O A) (hL : ∀ W, F W → Included L W) :
    Included L (intersection F) := fun x hx W hW => hL W hW x hx

def UpperBounds (F : InvariantSubspace T O A → Prop)
    (U : InvariantSubspace T O A) : Prop := ∀ W, F W → Included W U

theorem whole_is_upper (F : InvariantSubspace T O A → Prop) :
    UpperBounds F whole := fun _ _ _ _ => True.intro

def join (F : InvariantSubspace T O A → Prop) : InvariantSubspace T O A :=
  intersection (UpperBounds F)

theorem join_upper (F : InvariantSubspace T O A → Prop)
    (W : InvariantSubspace T O A) (hW : F W) : Included W (join F) :=
  fun x hx _U hU => hU W hW x hx

theorem join_least (F : InvariantSubspace T O A → Prop)
    (U : InvariantSubspace T O A) (hU : UpperBounds F U) : Included (join F) U :=
  intersection_lower (UpperBounds F) U hU

/-- The explicit universal properties of a complete lattice in the standard
inclusion order. Families are arbitrary Prop predicates, not finite lists. -/
def IsCompleteLattice : Prop :=
  (∀ U : InvariantSubspace T O A, Included U U) ∧
  (∀ U V W : InvariantSubspace T O A, Included U V → Included V W → Included U W) ∧
  (∀ U V : InvariantSubspace T O A, Included U V → Included V U → U = V) ∧
  ∀ F : InvariantSubspace T O A → Prop,
    (∀ W, F W → Included (intersection F) W) ∧
    (∀ L, (∀ W, F W → Included L W) → Included L (intersection F)) ∧
    (∀ W, F W → Included W (join F)) ∧
    (∀ U, (∀ W, F W → Included W U) → Included (join F) U)

theorem conjecture6825 (T : ClosedTopology X) (O : LinearOperations K X) (A : X → X) :
    IsCompleteLattice (T := T) (O := O) (A := A) := by
  refine ⟨included_refl, included_trans, included_antisymm, ?_⟩
  intro F
  exact ⟨intersection_lower F, intersection_greatest F, join_upper F, join_least F⟩

theorem empty_intersection_is_whole :
    intersection (T := T) (O := O) (A := A) (fun _ => False) = whole := by
  apply subspace_ext
  intro x
  constructor
  · intro _
    trivial
  · intro _ W h
    exact False.elim h

/-- The algebraic convention (subspaces need not be topologically closed)
is covered by the discrete topology, in which every subset is closed. -/
def discreteTopology (X : Type u) : ClosedTopology X where
  closed := fun _ => True
  empty_closed := True.intro
  univ_closed := True.intro
  union_closed := fun _ _ _ _ => True.intro
  intersection_closed := fun _ _ => True.intro

def integerOperations : LinearOperations Int Int where
  zero := 0
  add := (· + ·)
  smul := (· * ·)

theorem concrete_consistency_example :
    IsCompleteLattice (T := discreteTopology Int) (O := integerOperations)
      (A := fun n => 2 * n) := conjecture6825 _ _ _

#print axioms conjecture6825
#print axioms intersection_member
#print axioms empty_intersection_is_whole
#print axioms concrete_consistency_example
end Conjecture6825
