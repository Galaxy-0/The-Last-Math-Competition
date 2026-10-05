/-!
# Conjecture 00000009898 (torsion-class lattices): the forest criterion is false

The conjecture (paraphrased): *the lattice `tors A` of torsion classes of a finite-dimensional
algebra `A` is distributive **if and only if** the oriented path partial order of the quiver of `A`
is a forest order; the minimal counterexample to distributivity is the three-vertex oriented
cycle; and "the length of distributive approximations" is bounded.*

We refute the "if" direction (hence the "iff") and the minimality clause with the path algebra
`A = K(1 → 2)` of the quiver `A₂`, **over an arbitrary field `K`**:

* the path order of `A₂` is a 2-element chain, which is a forest order under every reading
  (`a2_forest`);
* `tors A` is **not** distributive (`not_distributive`), and the dual law fails too
  (`not_codistributive`);
* `A₂` has 2 vertices, fewer than the 3 of the oriented 3-cycle.

Everything is built from scratch in core Lean 4:

* `Fld K`: a field (all field axioms); instances `F₂ = Bool` and `F₃`.
* `Vec K n = Kⁿ`, linear maps `IsLin`.
* `Rep K`: finite-dimensional representations `V₁ --f--> V₂` of `A₂` (= finite-dimensional
  `KA₂`-modules), with `V₁ = K^{d₁}`, `V₂ = K^{d₂}` and `f` an arbitrary `K`-linear map.
* `Hom M N`: morphisms of representations (pairs of linear maps commuting with the arrow);
  surjective morphisms (epimorphisms = quotients), isomorphisms, short exact sequences.
* `IsTors T`: a torsion class = a class of representations containing `0`, closed under
  quotients (hence under isomorphism, `IsTors.iso_closed`) and under extensions.
* The lattice operations on torsion classes: meet = intersection (`meet`), join = the
  intersection of all torsion classes containing both (`join`); `meet_isTors`, `join_isTors`,
  `join_least`, ... show they are the lattice meet and join.
-/

namespace Tors

/-! ## 1. Fields -/

/-- A field, with all field axioms (the proofs below only use the additive group, `0 ≠ 1` and
`a * 0 = 0`, but we ask for a genuine field). -/
class Fld (K : Type) where
  zero : K
  one : K
  add : K → K → K
  neg : K → K
  mul : K → K → K
  inv : K → K
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  neg_add : ∀ a, add (neg a) a = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  mul_add : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one
  mul_inv : ∀ a, a ≠ zero → mul a (inv a) = one

section Field
variable {K : Type} [Fld K]

theorem add_zero' (a : K) : Fld.add a Fld.zero = a := by
  rw [Fld.add_comm]; exact Fld.zero_add a

theorem add_neg' (a : K) : Fld.add a (Fld.neg a) = Fld.zero := by
  rw [Fld.add_comm]; exact Fld.neg_add a

theorem add_left_cancel' {a b c : K} (h : Fld.add a b = Fld.add a c) : b = c := by
  have h' : Fld.add (Fld.neg a) (Fld.add a b) = Fld.add (Fld.neg a) (Fld.add a c) := by rw [h]
  rw [← Fld.add_assoc, ← Fld.add_assoc, Fld.neg_add, Fld.zero_add, Fld.zero_add] at h'
  exact h'

theorem mul_zero' (c : K) : Fld.mul c Fld.zero = Fld.zero := by
  have h : Fld.add (Fld.mul c Fld.zero) (Fld.mul c Fld.zero)
      = Fld.add (Fld.mul c Fld.zero) Fld.zero := by
    rw [← Fld.mul_add, Fld.zero_add, add_zero']
  exact add_left_cancel' h

end Field

/-! ## 2. Coordinate vector spaces `Kⁿ` and linear maps -/

abbrev Vec (K : Type) (n : Nat) : Type := Fin n → K

section Vec
variable {K : Type} [Fld K]

def vzero (K : Type) [Fld K] (n : Nat) : Vec K n := fun _ => Fld.zero
def vadd {n : Nat} (u v : Vec K n) : Vec K n := fun i => Fld.add (u i) (v i)
def vneg {n : Nat} (u : Vec K n) : Vec K n := fun i => Fld.neg (u i)
def vsmul {n : Nat} (c : K) (u : Vec K n) : Vec K n := fun i => Fld.mul c (u i)

theorem vadd_assoc {n : Nat} (u v w : Vec K n) : vadd (vadd u v) w = vadd u (vadd v w) :=
  funext fun i => Fld.add_assoc (u i) (v i) (w i)
theorem vadd_comm {n : Nat} (u v : Vec K n) : vadd u v = vadd v u :=
  funext fun i => Fld.add_comm (u i) (v i)
theorem vzero_add {n : Nat} (u : Vec K n) : vadd (vzero K n) u = u :=
  funext fun i => Fld.zero_add (u i)
theorem vadd_zero {n : Nat} (u : Vec K n) : vadd u (vzero K n) = u :=
  funext fun i => add_zero' (u i)
theorem vneg_add {n : Nat} (u : Vec K n) : vadd (vneg u) u = vzero K n :=
  funext fun i => Fld.neg_add (u i)
theorem vadd_neg {n : Nat} (u : Vec K n) : vadd u (vneg u) = vzero K n :=
  funext fun i => add_neg' (u i)
theorem vsmul_zero {n : Nat} (c : K) : vsmul c (vzero K n) = vzero K n :=
  funext fun _ => mul_zero' c

theorem vadd_left_cancel {n : Nat} {a b c : Vec K n} (h : vadd a b = vadd a c) : b = c := by
  have h' : vadd (vneg a) (vadd a b) = vadd (vneg a) (vadd a c) := by rw [h]
  rw [← vadd_assoc, ← vadd_assoc, vneg_add, vzero_add, vzero_add] at h'
  exact h'

theorem eq_vneg_of_vadd {n : Nat} {a b : Vec K n} (h : vadd a b = vzero K n) : a = vneg b := by
  apply vadd_left_cancel (a := b)
  rw [vadd_comm, h, vadd_neg]

theorem eq_of_vsub {n : Nat} {a b : Vec K n} (h : vadd a (vneg b) = vzero K n) : a = b := by
  have h' := congrArg (fun t => vadd t b) h
  simp only at h'
  rw [vadd_assoc, vneg_add, vadd_zero, vzero_add] at h'
  exact h'

omit [Fld K] in
/-- Every vector of `K⁰` is zero. -/
theorem vec0_eq {u v : Vec K 0} : u = v := funext fun i => i.elim0

/-- `K`-linear maps `Kᵃ → Kᵇ`. -/
structure IsLin {a b : Nat} (g : Vec K a → Vec K b) : Prop where
  map_add : ∀ u v, g (vadd u v) = vadd (g u) (g v)
  map_smul : ∀ (c : K) u, g (vsmul c u) = vsmul c (g u)

theorem IsLin.map_zero {a b : Nat} {g : Vec K a → Vec K b} (hg : IsLin g) :
    g (vzero K a) = vzero K b := by
  have h := hg.map_add (vzero K a) (vzero K a)
  rw [vzero_add] at h
  apply vadd_left_cancel (a := g (vzero K a))
  rw [vadd_zero]; exact h.symm

theorem IsLin.map_neg {a b : Nat} {g : Vec K a → Vec K b} (hg : IsLin g) (u : Vec K a) :
    g (vneg u) = vneg (g u) := by
  apply eq_vneg_of_vadd
  rw [← hg.map_add, vneg_add, hg.map_zero]

theorem IsLin.map_sub {a b : Nat} {g : Vec K a → Vec K b} (hg : IsLin g) (u v : Vec K a) :
    g (vadd u (vneg v)) = vadd (g u) (vneg (g v)) := by
  rw [hg.map_add, hg.map_neg]

theorem id_lin {a : Nat} : IsLin (fun v : Vec K a => v) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem zeroMap_lin {a b : Nat} : IsLin (fun _ : Vec K a => vzero K b) :=
  ⟨fun _ _ => (vzero_add _).symm, fun c _ => (vsmul_zero c).symm⟩

/-- Every map into `K⁰` is linear. -/
theorem lin_to0 {a : Nat} (g : Vec K a → Vec K 0) : IsLin g :=
  ⟨fun _ _ => vec0_eq, fun _ _ => vec0_eq⟩

/-- Every linear map out of `K⁰` is zero. -/
theorem lin_from0 {b : Nat} {g : Vec K 0 → Vec K b} (hg : IsLin g) (v : Vec K 0) :
    g v = vzero K b := by
  rw [show v = vzero K 0 from vec0_eq]; exact hg.map_zero

/-! Vertex-level exactness notions. -/

def VInj {a b : Nat} (g : Vec K a → Vec K b) : Prop := ∀ u u', g u = g u' → u = u'
def VSurj {a b : Nat} (g : Vec K a → Vec K b) : Prop := ∀ w, ∃ v, g v = w
/-- `Kᵃ --i--> Kᵇ --p--> Kᶜ` is exact at `Kᵇ`: `ker p = im i`. -/
def VExact {a b c : Nat} (i : Vec K a → Vec K b) (p : Vec K b → Vec K c) : Prop :=
  ∀ v, p v = vzero K c ↔ ∃ u, i u = v

/-! The split sequence `0 → K → K^{n+1} → Kⁿ → 0` (first coordinate, then the rest). -/

/-- `c ↦ (c, 0, …, 0)`. -/
def ins0 {n : Nat} (c : Vec K 1) : Vec K (n + 1) :=
  fun j => if j.val = 0 then c ⟨0, by omega⟩ else Fld.zero

/-- `(w₀, w₁, …, wₙ) ↦ (w₁, …, wₙ)`. -/
def tl {n : Nat} (w : Vec K (n + 1)) : Vec K n := fun j => w j.succ

theorem ins0_lin {n : Nat} : IsLin (ins0 (K := K) (n := n)) := by
  constructor
  · intro u v; funext j
    by_cases h : j.val = 0
    · simp [ins0, vadd, h]
    · simp [ins0, vadd, h, Fld.zero_add]
  · intro c u; funext j
    by_cases h : j.val = 0
    · simp [ins0, vsmul, h]
    · simp [ins0, vsmul, h, mul_zero']

theorem tl_lin {n : Nat} : IsLin (tl (K := K) (n := n)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem ins0_inj {n : Nat} : VInj (ins0 (K := K) (n := n)) := by
  intro u u' h; funext k
  have hk : k = ⟨0, by omega⟩ := Fin.ext (by omega)
  have := congrFun h ⟨0, by omega⟩
  simp [ins0] at this
  rw [hk]; exact this

theorem tl_surj {n : Nat} : VSurj (tl (K := K) (n := n)) := by
  intro w
  refine ⟨fun j => if h : j.val = 0 then Fld.zero else w ⟨j.val - 1, by omega⟩, ?_⟩
  funext j
  simp [tl, Fin.val_succ]

theorem ins0_tl_exact {n : Nat} : VExact (ins0 (K := K) (n := n)) tl := by
  intro w
  constructor
  · intro h
    refine ⟨fun _ => w ⟨0, by omega⟩, ?_⟩
    funext j
    by_cases hj : j.val = 0
    · simp only [ins0, hj, if_true]
      exact congrArg w (Fin.ext (by show 0 = j.val; omega))
    · simp only [ins0, hj, if_false]
      have e : j = (⟨j.val - 1, by omega⟩ : Fin n).succ := Fin.ext (by simp [Fin.val_succ]; omega)
      have := congrFun h ⟨j.val - 1, by omega⟩
      simp only [tl, vzero] at this
      rw [e, this]
  · rintro ⟨c, rfl⟩
    funext j
    simp [tl, ins0, vzero, Fin.val_succ]

end Vec

/-! ## 3. Representations of `A₂ = (1 → 2)` and their morphisms -/

/-- A finite-dimensional representation `V₁ --f--> V₂` of the quiver `A₂ : 1 → 2` over `K`,
i.e. a finite-dimensional module over the path algebra `K A₂`.  (Every finite-dimensional vector
space is isomorphic to some `Kᵈ`, so this is a skeleton of `mod KA₂` up to isomorphism.) -/
structure Rep (K : Type) [Fld K] where
  d1 : Nat
  d2 : Nat
  f : Vec K d1 → Vec K d2
  f_lin : IsLin f

section Reps
variable {K : Type} [Fld K]

/-- Morphisms of representations: linear maps at each vertex commuting with the arrow. -/
structure Hom (M N : Rep K) where
  g1 : Vec K M.d1 → Vec K N.d1
  g2 : Vec K M.d2 → Vec K N.d2
  lin1 : IsLin g1
  lin2 : IsLin g2
  comm : ∀ v, N.f (g1 v) = g2 (M.f v)

/-- An epimorphism `M ↠ N`: `N` is a quotient (factor module) of `M`. -/
def Surj {M N : Rep K} (p : Hom M N) : Prop := VSurj p.g1 ∧ VSurj p.g2

/-- `0 → L --i--> M --p--> N → 0` is a short exact sequence. -/
structure ShortExact {L M N : Rep K} (i : Hom L M) (p : Hom M N) : Prop where
  inj1 : VInj i.g1
  inj2 : VInj i.g2
  exact1 : VExact i.g1 p.g1
  exact2 : VExact i.g2 p.g2
  surj1 : VSurj p.g1
  surj2 : VSurj p.g2

/-- Isomorphism of representations. -/
def Iso (M N : Rep K) : Prop :=
  ∃ (φ : Hom M N) (ψ : Hom N M), (∀ v, ψ.g1 (φ.g1 v) = v) ∧ (∀ v, ψ.g2 (φ.g2 v) = v) ∧
    (∀ w, φ.g1 (ψ.g1 w) = w) ∧ (∀ w, φ.g2 (ψ.g2 w) = w)

/-- Classes (full subcategories) of representations. -/
abbrev Cls (K : Type) [Fld K] : Type := Rep K → Prop

/-- The zero representation. -/
def zeroRep : Rep K := ⟨0, 0, fun _ => vzero K 0, zeroMap_lin⟩

/-- A torsion class: contains `0`, closed under quotients and under extensions. -/
structure IsTors (T : Cls K) : Prop where
  zero_mem : T zeroRep
  quot : ∀ {M N : Rep K} (p : Hom M N), Surj p → T M → T N
  ext : ∀ {L M N : Rep K} (i : Hom L M) (p : Hom M N), ShortExact i p → T L → T N → T M

/-- Torsion classes are closed under isomorphism. -/
theorem IsTors.iso_closed {T : Cls K} (hT : IsTors T) {M N : Rep K} (h : Iso M N)
    (hM : T M) : T N := by
  obtain ⟨φ, ψ, -, -, h3, h4⟩ := h
  exact hT.quot φ ⟨fun w => ⟨ψ.g1 w, h3 w⟩, fun w => ⟨ψ.g2 w, h4 w⟩⟩ hM

/-! ### The lattice operations on torsion classes -/

def meet (T U : Cls K) : Cls K := fun M => T M ∧ U M

/-- The join: the smallest torsion class containing `T ∪ U`. -/
def join (T U : Cls K) : Cls K :=
  fun M => ∀ W : Cls K, IsTors W → (∀ X, T X → W X) → (∀ X, U X → W X) → W M

theorem meet_isTors {T U : Cls K} (hT : IsTors T) (hU : IsTors U) : IsTors (meet T U) :=
  ⟨⟨hT.zero_mem, hU.zero_mem⟩,
   fun p hp hM => ⟨hT.quot p hp hM.1, hU.quot p hp hM.2⟩,
   fun i p hs hL hN => ⟨hT.ext i p hs hL.1 hN.1, hU.ext i p hs hL.2 hN.2⟩⟩

theorem join_isTors (T U : Cls K) : IsTors (join T U) :=
  ⟨fun _ hW _ _ => hW.zero_mem,
   fun p hp hM W hW hTW hUW => hW.quot p hp (hM W hW hTW hUW),
   fun i p hs hL hN W hW hTW hUW => hW.ext i p hs (hL W hW hTW hUW) (hN W hW hTW hUW)⟩

theorem le_join_left (T U : Cls K) : ∀ X, T X → join T U X :=
  fun _ h _ _ hTW _ => hTW _ h
theorem le_join_right (T U : Cls K) : ∀ X, U X → join T U X :=
  fun _ h _ _ _ hUW => hUW _ h
theorem join_least {T U W : Cls K} (hW : IsTors W) (hTW : ∀ X, T X → W X)
    (hUW : ∀ X, U X → W X) : ∀ X, join T U X → W X :=
  fun _ h => h W hW hTW hUW

/-- Distributivity of the lattice `tors (K A₂)`. -/
def Distributive (K : Type) [Fld K] : Prop :=
  ∀ a b c : Cls K, IsTors a → IsTors b → IsTors c →
    ∀ M, meet a (join b c) M ↔ join (meet a b) (meet a c) M

/-- The dual distributive law (equivalent for lattices; we refute both forms directly). -/
def CoDistributive (K : Type) [Fld K] : Prop :=
  ∀ a b c : Cls K, IsTors a → IsTors b → IsTors c →
    ∀ M, join a (meet b c) M ↔ meet (join a b) (join a c) M

/-! ## 4. The objects: simples, projectives, and five torsion classes -/

/-- `S₁ⁿ = (Kⁿ → 0)`. -/
def S1pow (n : Nat) : Rep K := ⟨n, 0, fun _ => vzero K 0, zeroMap_lin⟩
/-- `S₂ⁿ = (0 → Kⁿ)`. -/
def S2pow (n : Nat) : Rep K := ⟨0, n, fun _ => vzero K n, zeroMap_lin⟩
/-- The simple `S₁ = (K → 0)`. -/
def S1 : Rep K := S1pow 1
/-- The simple (and projective) `S₂ = P₂ = (0 → K)`. -/
def S2 : Rep K := S2pow 1
/-- The projective-injective `P₁ = I₂ = (K --id--> K)`. -/
def P1 : Rep K := ⟨1, 1, fun v => v, id_lin⟩

/-- `x = {V₂ = 0} = add S₁`. -/
def xC : Cls K := fun M => ∀ v : Vec K M.d2, v = vzero K M.d2
/-- `y = {f surjective} = add {S₁, P₁}`. -/
def yC : Cls K := fun M => ∀ w : Vec K M.d2, ∃ v, M.f v = w
/-- `z = {V₁ = 0} = add S₂`. -/
def zC : Cls K := fun M => ∀ v : Vec K M.d1, v = vzero K M.d1
/-- `0` (the zero representations). -/
def botC : Cls K := meet zC xC
/-- `mod A`. -/
def topC : Cls K := fun _ => True

theorem xC_isTors : IsTors (xC (K := K)) := by
  refine ⟨fun _ => vec0_eq, ?_, ?_⟩
  · intro M N p hp hM w
    obtain ⟨v, rfl⟩ := hp.2 w
    rw [hM v]; exact p.lin2.map_zero
  · intro L M N i p hs hL hN v
    obtain ⟨u, rfl⟩ := (hs.exact2 v).1 (hN _)
    rw [hL u]; exact i.lin2.map_zero

theorem zC_isTors : IsTors (zC (K := K)) := by
  refine ⟨fun _ => vec0_eq, ?_, ?_⟩
  · intro M N p hp hM w
    obtain ⟨v, rfl⟩ := hp.1 w
    rw [hM v]; exact p.lin1.map_zero
  · intro L M N i p hs hL hN v
    obtain ⟨u, rfl⟩ := (hs.exact1 v).1 (hN _)
    rw [hL u]; exact i.lin1.map_zero

theorem yC_isTors : IsTors (yC (K := K)) := by
  refine ⟨fun _ => ⟨vzero K 0, vec0_eq⟩, ?_, ?_⟩
  · -- quotients: w = p₂ v = p₂ (f u) = f (p₁ u)
    intro M N p hp hM w
    obtain ⟨v, rfl⟩ := hp.2 w
    obtain ⟨u, rfl⟩ := hM v
    exact ⟨p.g1 u, p.comm u⟩
  · -- extensions
    intro L M N i p hs hL hN w
    obtain ⟨a, ha⟩ := hN (p.g2 w)
    obtain ⟨b, rfl⟩ := hs.surj1 a
    -- p₂ (w - f b) = 0
    have h0 : p.g2 (vadd w (vneg (M.f b))) = vzero K N.d2 := by
      rw [p.lin2.map_sub, ← p.comm b, ha, vadd_neg]
    obtain ⟨c, hc⟩ := (hs.exact2 _).1 h0
    obtain ⟨d, rfl⟩ := hL c
    refine ⟨vadd b (i.g1 d), ?_⟩
    rw [M.f_lin.map_add, i.comm d, hc, vadd_comm (M.f b), vadd_assoc, vneg_add, vadd_zero]

theorem botC_isTors : IsTors (botC (K := K)) := meet_isTors zC_isTors xC_isTors

theorem topC_isTors : IsTors (topC (K := K)) :=
  ⟨trivial, fun _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

/-! ### Membership of the indecomposables -/

/-- The vector `(1)` in `K¹`. -/
def e1 : Vec K 1 := fun _ => Fld.one

theorem e1_ne : e1 ≠ vzero K 1 := by
  intro h
  exact Fld.zero_ne_one (congrFun h ⟨0, by omega⟩).symm

theorem S1_x : xC (S1 (K := K)) := fun _ => vec0_eq
theorem S1_y : yC (S1 (K := K)) := fun _ => ⟨vzero K 1, vec0_eq⟩
theorem S1_not_z : ¬ zC (S1 (K := K)) := fun h => e1_ne (h e1)
theorem S2_z : zC (S2 (K := K)) := fun _ => vec0_eq
theorem S2_not_x : ¬ xC (S2 (K := K)) := fun h => e1_ne (h e1)
theorem S2_not_y : ¬ yC (S2 (K := K)) := by
  intro h
  obtain ⟨v, hv⟩ := h e1
  exact e1_ne hv.symm
theorem P1_y : yC (P1 (K := K)) := fun w => ⟨w, rfl⟩
theorem P1_not_x : ¬ xC (P1 (K := K)) := fun h => e1_ne (h e1)
theorem P1_not_z : ¬ zC (P1 (K := K)) := fun h => e1_ne (h e1)

/-- The torsion classes `0, x, y, z, mod A` form a pentagon `N₅`:
`0 < x < y < mod A`, `0 < z < mod A`, `z` incomparable with `x` and `y`. -/
theorem pentagon :
    (∀ M : Rep K, botC M → xC M) ∧ (∀ M : Rep K, xC M → yC M) ∧
    (∀ M : Rep K, botC M → zC M) ∧
    xC (S1 (K := K)) ∧ ¬ botC (S1 (K := K)) ∧
    yC (P1 (K := K)) ∧ ¬ xC (P1 (K := K)) ∧
    zC (S2 (K := K)) ∧ ¬ yC (S2 (K := K)) ∧ ¬ zC (S1 (K := K)) := by
  refine ⟨fun _ h => h.2, ?_, fun _ h => h.1, S1_x, fun h => S1_not_z h.1, P1_y, P1_not_x, S2_z,
    S2_not_y, S1_not_z⟩
  intro M hM w
  exact ⟨vzero K M.d1, by rw [hM w, hM (M.f _)]⟩

/-! ## 5. A torsion class containing `S₁` and `S₂` is everything -/

/-- The zero morphism between two representations with `d₁ = d₂ = 0` is surjective. -/
theorem S2pow_zero_mem {T : Cls K} (hT : IsTors T) : T (S2pow 0) := by
  let p : Hom (zeroRep (K := K)) (S2pow 0) :=
    ⟨fun v => v, fun v => v, id_lin, id_lin, fun _ => vec0_eq⟩
  exact hT.quot p ⟨fun w => ⟨w, rfl⟩, fun w => ⟨w, rfl⟩⟩ hT.zero_mem

theorem S1pow_zero_mem {T : Cls K} (hT : IsTors T) : T (S1pow 0) := by
  let p : Hom (zeroRep (K := K)) (S1pow 0) :=
    ⟨fun v => v, fun v => v, id_lin, id_lin, fun _ => vec0_eq⟩
  exact hT.quot p ⟨fun w => ⟨w, rfl⟩, fun w => ⟨w, rfl⟩⟩ hT.zero_mem

/-- `0 → S₁ → S₁^{n+1} → S₁ⁿ → 0`. -/
theorem S1pow_mem {T : Cls K} (hT : IsTors T) (h1 : T S1) : ∀ n, T (S1pow n)
  | 0 => S1pow_zero_mem hT
  | n + 1 => by
    let i : Hom (S1 (K := K)) (S1pow (n + 1)) :=
      ⟨ins0, fun v => v, ins0_lin, id_lin, fun _ => vec0_eq⟩
    let p : Hom (S1pow (K := K) (n + 1)) (S1pow n) :=
      ⟨tl, fun v => v, tl_lin, id_lin, fun _ => vec0_eq⟩
    have hs : ShortExact i p :=
      ⟨ins0_inj, fun _ _ h => h, ins0_tl_exact,
       fun v => ⟨fun _ => ⟨v, rfl⟩, fun _ => vec0_eq⟩, tl_surj, fun w => ⟨w, rfl⟩⟩
    exact hT.ext i p hs h1 (S1pow_mem hT h1 n)

/-- `0 → S₂ → S₂^{n+1} → S₂ⁿ → 0`. -/
theorem S2pow_mem {T : Cls K} (hT : IsTors T) (h2 : T S2) : ∀ n, T (S2pow n)
  | 0 => S2pow_zero_mem hT
  | n + 1 => by
    let i : Hom (S2 (K := K)) (S2pow (n + 1)) :=
      ⟨fun v => v, ins0, id_lin, ins0_lin, fun _ => (ins0_lin.map_zero).symm⟩
    let p : Hom (S2pow (K := K) (n + 1)) (S2pow n) :=
      ⟨fun v => v, tl, id_lin, tl_lin, fun _ => (tl_lin.map_zero).symm⟩
    have hs : ShortExact i p :=
      ⟨fun _ _ h => h, ins0_inj, fun v => ⟨fun _ => ⟨v, rfl⟩, fun _ => vec0_eq⟩,
       ins0_tl_exact, fun w => ⟨w, rfl⟩, tl_surj⟩
    exact hT.ext i p hs h2 (S2pow_mem hT h2 n)

/-- Every representation `M` is an extension `0 → S₂^{d₂} → M → S₁^{d₁} → 0`, so a torsion
class containing `S₁` and `S₂` contains every representation. -/
theorem all_of_S1_S2 {T : Cls K} (hT : IsTors T) (h1 : T S1) (h2 : T S2) : ∀ M, T M := by
  intro M
  let i : Hom (S2pow (K := K) M.d2) M :=
    ⟨fun _ => vzero K M.d1, fun v => v, zeroMap_lin, id_lin,
     fun _ => M.f_lin.map_zero⟩
  let p : Hom M (S1pow (K := K) M.d1) :=
    ⟨fun v => v, fun _ => vzero K 0, id_lin, zeroMap_lin, fun _ => vec0_eq⟩
  have hs : ShortExact i p :=
    ⟨fun _ _ _ => vec0_eq, fun _ _ h => h,
     fun v => ⟨fun h => ⟨vzero K 0, h.symm⟩, fun ⟨_, hu⟩ => hu.symm⟩,
     fun v => ⟨fun _ => ⟨v, rfl⟩, fun _ => rfl⟩,
     fun w => ⟨w, rfl⟩, fun _ => ⟨vzero K M.d2, vec0_eq⟩⟩
  exact hT.ext i p hs (S2pow_mem hT h2 _) (S1pow_mem hT h1 _)

/-! ## 6. The lattice computations and the failure of distributivity -/

/-- `x ∨ z = mod A`. -/
theorem join_x_z : ∀ M : Rep K, join xC zC M :=
  fun M _ hW hx hz => all_of_S1_S2 hW (hx _ S1_x) (hz _ S2_z) M

/-- `y ∧ z = 0`: if `V₁ = 0` and `f : V₁ ↠ V₂`, then `V₂ = 0`. -/
theorem meet_y_z : ∀ M : Rep K, meet yC zC M → botC M := by
  intro M ⟨hy, hz⟩
  refine ⟨hz, fun w => ?_⟩
  obtain ⟨v, rfl⟩ := hy w
  rw [hz v]; exact M.f_lin.map_zero

/-- `(y ∧ x) ∨ (y ∧ z) ≤ x`. -/
theorem join_meets_le_x : ∀ M : Rep K, join (meet yC xC) (meet yC zC) M → xC M :=
  join_least xC_isTors (fun _ h => h.2) (fun M h => (meet_y_z M h).2)

/-- **The torsion-class lattice of `K A₂` is not distributive** (any field `K`):
with `a = y, b = x, c = z` and the witness `M = P₁`,
`P₁ ∈ y ∧ (x ∨ z) = y` but `P₁ ∉ (y ∧ x) ∨ (y ∧ z) = x`. -/
theorem not_distributive (K : Type) [Fld K] : ¬ Distributive K := by
  intro h
  have hl : meet yC (join xC zC) (P1 (K := K)) := ⟨P1_y, join_x_z _⟩
  have hr := (h yC xC zC yC_isTors xC_isTors zC_isTors P1).1 hl
  exact P1_not_x (join_meets_le_x _ hr)

/-- The dual law fails as well: `x ∨ (y ∧ z) = x` but `(x ∨ y) ∧ (x ∨ z) = y ∋ P₁`. -/
theorem not_codistributive (K : Type) [Fld K] : ¬ CoDistributive K := by
  intro h
  have hr : meet (join xC yC) (join xC zC) (P1 (K := K)) :=
    ⟨le_join_right _ _ _ P1_y, join_x_z _⟩
  have hl := (h xC yC zC xC_isTors yC_isTors zC_isTors P1).2 hr
  exact P1_not_x (join_least xC_isTors (fun _ h => h) (fun M h => (meet_y_z M h).2) _ hl)

/-! ### Non-vacuity of the torsion-class predicate -/

/-- `{M | f injective} = add {S₂, P₁}` is **not** a torsion class: `P₁ ↠ S₁`. -/
def injC : Cls K := fun M => VInj M.f

theorem injC_not_tors : ¬ IsTors (injC (K := K)) := by
  intro h
  let p : Hom (P1 (K := K)) S1 := ⟨fun v => v, fun _ => vzero K 0, id_lin, zeroMap_lin,
    fun _ => vec0_eq⟩
  have hS1 : injC (S1 (K := K)) := h.quot p ⟨fun w => ⟨w, rfl⟩, fun _ => ⟨e1, vec0_eq⟩⟩
    (fun _ _ h => h)
  exact e1_ne (hS1 e1 (vzero K 1) vec0_eq)

/-- All five members of the pentagon are torsion classes, and `injC` is not. -/
theorem five_tors :
    IsTors (botC (K := K)) ∧ IsTors (xC (K := K)) ∧ IsTors (yC (K := K)) ∧
    IsTors (zC (K := K)) ∧ IsTors (topC (K := K)) ∧ ¬ IsTors (injC (K := K)) :=
  ⟨botC_isTors, xC_isTors, yC_isTors, zC_isTors, topC_isTors, injC_not_tors⟩

end Reps

/-! ## 7. Quivers, the path order and forest orders -/

/-- A finite quiver: vertices `0, …, n-1`, arrows `(source, target)`. -/
structure Quiver where
  n : Nat
  arrows : List (Nat × Nat)

/-- Oriented paths: `Path Q i j` iff there is an oriented path `i → ⋯ → j` (length `≥ 0`).
This is the (pre)order "`i ≤ j` iff there is an oriented path from `i` to `j`". -/
inductive Path (Q : Quiver) : Nat → Nat → Prop
  | refl (i : Nat) : Path Q i i
  | cons {i j k : Nat} : (i, j) ∈ Q.arrows → Path Q j k → Path Q i k

/-- A forest order, in the strongest sense: the path relation is a partial order (antisymmetric)
and **both** every down-set and every up-set is a chain.  (Any weaker reading of "forest order",
e.g. only down-sets, only up-sets, or a Hasse diagram without cycles, is implied for `A₂`.) -/
structure ForestOrder (Q : Quiver) : Prop where
  antisymm : ∀ i j, i < Q.n → j < Q.n → Path Q i j → Path Q j i → i = j
  down_chain : ∀ v i j, v < Q.n → i < Q.n → j < Q.n →
    Path Q i v → Path Q j v → Path Q i j ∨ Path Q j i
  up_chain : ∀ v i j, v < Q.n → i < Q.n → j < Q.n →
    Path Q v i → Path Q v j → Path Q i j ∨ Path Q j i

/-- The quiver `A₂ : 0 → 1` (vertices `1, 2` of the text are `0, 1` here). -/
def A2Q : Quiver := ⟨2, [(0, 1)]⟩

/-- The oriented 3-cycle `0 → 1 → 2 → 0`. -/
def C3Q : Quiver := ⟨3, [(0, 1), (1, 2), (2, 0)]⟩

theorem a2_path_iff (i j : Nat) : Path A2Q i j ↔ i = j ∨ (i = 0 ∧ j = 1) := by
  constructor
  · intro h
    induction h with
    | refl i => exact Or.inl rfl
    | cons ha _ ih =>
      simp [A2Q] at ha
      obtain ⟨rfl, rfl⟩ := ha
      rcases ih with h | ⟨h, _⟩
      · exact Or.inr ⟨rfl, h.symm⟩
      · exact absurd h (by decide)
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact Path.refl _
    · exact Path.cons (by simp [A2Q]) (Path.refl 1)

/-- The path order of `A₂` is the 2-chain `0 < 1`, a forest order. -/
theorem a2_forest : ForestOrder A2Q := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp only [a2_path_iff] at * <;> simp only [A2Q] at * <;> omega

/-- The oriented 3-cycle has 3 vertices and its path relation is not even antisymmetric. -/
theorem c3_facts : C3Q.n = 3 ∧ ¬ ForestOrder C3Q := by
  refine ⟨rfl, fun h => ?_⟩
  have h01 : Path C3Q 0 1 := Path.cons (by simp [C3Q]) (Path.refl 1)
  have h10 : Path C3Q 1 0 :=
    Path.cons (j := 2) (by simp [C3Q]) (Path.cons (by simp [C3Q]) (Path.refl 0))
  exact absurd (h.antisymm 0 1 (by decide) (by decide) h01 h10) (by decide)

/-! ## 8. The conjecture's clauses, instantiated at `A = K A₂`, and their refutation -/

/-- "If" direction of the criterion at `A = K A₂`: forest path order ⇒ `tors A` distributive. -/
def IfClause (K : Type) [Fld K] : Prop := ForestOrder A2Q → Distributive K

/-- The criterion itself ("iff") at `A = K A₂`. -/
def IffClause (K : Type) [Fld K] : Prop := Distributive K ↔ ForestOrder A2Q

/-- "The minimal counterexample to distributivity is the 3-vertex oriented cycle": in
particular every algebra whose quiver has fewer than 3 vertices has a distributive `tors`. -/
def MinClause (K : Type) [Fld K] : Prop := A2Q.n < C3Q.n → Distributive K

/-- **Main theorem.** Over every field `K`, the "if" direction of the criterion fails for
`A = K A₂`. -/
theorem conjecture_00000009898_false (K : Type) [Fld K] : ¬ IfClause K :=
  fun h => not_distributive K (h a2_forest)

theorem iffClause_false (K : Type) [Fld K] : ¬ IffClause K :=
  fun h => not_distributive K (h.2 a2_forest)

theorem minClause_false (K : Type) [Fld K] : ¬ MinClause K :=
  fun h => not_distributive K (h (by decide))

/-! ## 9. Fields: `F₂` and `F₃` (non-vacuity of `Fld`) -/

instance fldBool : Fld Bool where
  zero := false
  one := true
  add := xor
  neg := id
  mul := and
  inv := id
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  neg_add := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_add := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_ne_one := by decide
  mul_inv := by intro a h; cases a <;> simp_all

/-- The field with three elements. -/
inductive F3 | z | o | t
  deriving DecidableEq

def F3.add : F3 → F3 → F3
  | .z, b => b
  | a, .z => a
  | .o, .o => .t
  | .o, .t => .z
  | .t, .o => .z
  | .t, .t => .o

def F3.mul : F3 → F3 → F3
  | .z, _ => .z
  | _, .z => .z
  | .o, b => b
  | a, .o => a
  | .t, .t => .o

def F3.neg : F3 → F3
  | .z => .z
  | .o => .t
  | .t => .o

instance fldF3 : Fld F3 where
  zero := .z
  one := .o
  add := F3.add
  neg := F3.neg
  mul := F3.mul
  inv := id
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  zero_add := by intro a; cases a <;> rfl
  neg_add := by intro a; cases a <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_add := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_ne_one := by decide
  mul_inv := by intro a h; cases a <;> first | rfl | exact absurd rfl h

/-- Instances: over `F₂` and over `F₃`. -/
theorem conjecture_false_F2 : ¬ IfClause Bool := conjecture_00000009898_false Bool
theorem conjecture_false_F3 : ¬ IfClause F3 := conjecture_00000009898_false F3

end Tors

#print axioms Tors.conjecture_00000009898_false
#print axioms Tors.iffClause_false
#print axioms Tors.minClause_false
#print axioms Tors.not_distributive
#print axioms Tors.not_codistributive
#print axioms Tors.all_of_S1_S2
#print axioms Tors.five_tors
#print axioms Tors.pentagon
#print axioms Tors.a2_forest
#print axioms Tors.c3_facts
#print axioms Tors.conjecture_false_F2
#print axioms Tors.conjecture_false_F3
