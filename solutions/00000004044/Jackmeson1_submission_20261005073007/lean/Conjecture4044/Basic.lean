import Mathlib

/-!
# Conjecture 00000004044 is false

Conjecture 00000004044 reads:

> Definition: HH^1 is the Lie algebra of outer derivations, the first Hochschild cohomology.
> Conjecture: The HH^1 of a quiver algebra is solvable if and only if its oriented cycles are all
> broken after removing at most one vertex; the decision table is complete for n <= 6 and the
> formula holds for all n.

We refute the "if" direction with the generalized Kronecker quiver `K₃`: two vertices `1, 2` and
three parallel arrows `α₀ α₁ α₂ : 1 → 2`. It has no oriented cycle at all, so its cycles are
broken after removing zero vertices; but over every field `k` the Lie algebra
`HH¹(kK₃) = Der(kK₃) / Inn(kK₃)` is not solvable.

Definitions (general, for any associative unital algebra `A` over a commutative ring `k`):
* `Der k A`: the `k`-linear maps `D : A → A` with `D (x * y) = D x * y + x * D y`, a Lie subalgebra
  of `Module.End k A` under the commutator bracket `⁅D, E⁆ = D ∘ E - E ∘ D`.
  (Mathlib's `Derivation` requires a commutative algebra, so we cannot use it here.)
* `Inn k A`: the inner derivations `ad a = (x ↦ a * x - x * a)`, a Lie ideal of `Der k A`.
* `HH1 k A := Der k A ⧸ Inn k A`, the Lie algebra of outer derivations
  (= the first Hochschild cohomology `HH¹(A, A)`), with Mathlib's quotient Lie algebra structure.
* Solvability is Mathlib's `LieAlgebra.IsSolvable` (the derived series reaches `0`).

The path algebra `kK₃` (`PathAlg k`) is the `k`-vector space of functions on the set `P` of all
paths of `K₃` (the trivial paths `e₁, e₂` and the arrows `α₀, α₁, α₂`; `paths_bijective` checks
against Mathlib's `Quiver.Path` that these are all the paths), with the product of two paths equal
to their concatenation when it is defined and `0` otherwise (`basis_mul_basis`). Paths are
composed left to right, as in Mathlib's `Quiver.Path.comp`: `e₁ * αᵢ = αᵢ = αᵢ * e₂`.

Proof: for `i ≠ j` let `D i j` be the derivation sending `αⱼ ↦ αᵢ` and killing `e₁, e₂` and the
other arrows (the elementary matrix `E_ij` acting on the arrow space). For distinct `i, j, m`,
`⁅D i m, D m j⁆ = D i j`, so the classes `d i j` in `HH¹` lie in every term of the derived series.
`D 0 1` is not inner (an inner derivation sends each arrow `αⱼ` to a multiple of `αⱼ`), so `d 0 1 ≠ 0`
and the derived series never reaches `0`.
-/

namespace C4044

open LieAlgebra

/- As in Mathlib's Lie theory files: an associative ring is a Lie ring under the commutator
`⁅x, y⁆ = x * y - y * x` (Mathlib makes this a local instance to avoid diamonds). -/
attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## First Hochschild cohomology as the Lie algebra of outer derivations -/

section HH

variable (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A]

/-- The `k`-linear derivations of the associative algebra `A`, as a Lie subalgebra of
`Module.End k A` (commutator bracket). -/
def Der : LieSubalgebra k (Module.End k A) where
  carrier := {D | ∀ x y : A, D (x * y) = D x * y + x * D y}
  zero_mem' := by intro x y; simp
  add_mem' := by
    intro D E hD hE x y
    simp only [Set.mem_ofPred_eq] at hD hE
    simp only [LinearMap.add_apply, hD x y, hE x y, add_mul, mul_add]
    abel
  smul_mem' := by
    intro c D hD x y
    simp only [Set.mem_ofPred_eq] at hD
    simp only [LinearMap.smul_apply, hD x y, smul_add, smul_mul_assoc, mul_smul_comm]
  lie_mem' := by
    intro D E hD hE x y
    simp only [Set.mem_ofPred_eq] at hD hE
    simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      hD, hE, map_add]
    noncomm_ring

/-- The inner derivation `ad a : x ↦ a * x - x * a`. -/
def ad (a : A) : Module.End k A := LinearMap.mulLeft k a - LinearMap.mulRight k a

@[simp] lemma ad_apply (a x : A) : ad k A a x = a * x - x * a := rfl

/-- Every `ad a` is a derivation. -/
lemma ad_mem_Der (a : A) : ad k A a ∈ Der k A := by
  intro x y
  simp only [ad_apply]
  noncomm_ring

/-- The inner derivations `{ad a | a ∈ A}`, a Lie ideal of `Der k A`. -/
def Inn : LieIdeal k (Der k A) where
  carrier := {D | ∃ a : A, (D : Module.End k A) = ad k A a}
  add_mem' := by
    rintro D E ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    change (D : Module.End k A) + E = _
    rw [ha, hb]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, ad_apply]
    noncomm_ring
  zero_mem' := ⟨0, LinearMap.ext fun x => by simp⟩
  smul_mem' := by
    rintro c D ⟨a, ha⟩
    refine ⟨c • a, ?_⟩
    change c • (D : Module.End k A) = _
    rw [ha]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.smul_apply, ad_apply, smul_sub, smul_mul_assoc, mul_smul_comm]
  lie_mem := by
    rintro D E ⟨a, ha⟩
    refine ⟨(D : Module.End k A) a, LinearMap.ext fun x => ?_⟩
    have hD : ∀ x y : A, (D : Module.End k A) (x * y) =
        (D : Module.End k A) x * y + x * (D : Module.End k A) y := D.2
    simp only [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket,
      LinearMap.sub_apply, Module.End.mul_apply, ha, ad_apply, map_sub, hD]
    noncomm_ring

/-- `HH¹(A) = Der(A) / Inn(A)`, the Lie algebra of outer derivations. -/
abbrev HH1 := Der k A ⧸ Inn k A

end HH

/-! ## The generalized Kronecker quiver `K₃` -/

/-- The two vertices of `K₃`. -/
inductive V | one | two
  deriving DecidableEq

/-- `K₃` as a Mathlib quiver: three arrows `1 → 2` and no other arrows. -/
instance : Quiver V where
  Hom a b := match a, b with
    | .one, .two => Fin 3
    | _, _ => PEmpty

/-- `p` passes through the vertex `v` (as its source or any later vertex). -/
def visits {W : Type*} [Quiver W] {a : W} : {b : W} → Quiver.Path a b → W → Prop
  | _, .nil, v => v = a
  | b, .cons p _, v => visits p v ∨ v = b

/-- All oriented cycles (closed paths of positive length) are broken after removing at most one
vertex: some set `S` of at most one vertex meets every oriented cycle. -/
def CyclesBrokenByAtMostOneVertex (W : Type*) [Quiver W] : Prop :=
  ∃ S : Set W, S.Subsingleton ∧
    ∀ (w : W) (p : Quiver.Path w w), 0 < p.length → ∃ v ∈ S, visits p v

lemma path_shape : ∀ {a b : V} (p : Quiver.Path a b),
    p.length = 0 ∨ (a = .one ∧ b = .two ∧ p.length = 1)
  | _, _, .nil => Or.inl rfl
  | a, b, .cons (b := c) p e => by
    rcases path_shape p with h | ⟨_, hc, _⟩
    · have hac := Quiver.Path.eq_of_length_zero p h
      subst hac
      cases a <;> cases b
      · exact (e : PEmpty).elim
      · exact Or.inr ⟨rfl, rfl, by simp [h]⟩
      · exact (e : PEmpty).elim
      · exact (e : PEmpty).elim
    · subst hc
      cases b <;> exact (e : PEmpty).elim

/-- `K₃` has no oriented cycles. -/
theorem K3_no_oriented_cycle (w : V) (p : Quiver.Path w w) : p.length = 0 := by
  rcases path_shape p with h | ⟨h1, h2, _⟩
  · exact h
  · exact absurd (h1.symm.trans h2) (by decide)

theorem K3_cyclesBroken : CyclesBrokenByAtMostOneVertex V :=
  ⟨∅, Set.subsingleton_empty, fun w p hp => by simp [K3_no_oriented_cycle w p] at hp⟩

/-! ## The path algebra `kK₃` -/

/-- The paths of `K₃`: the trivial path `e v` at each vertex and the three arrows. -/
inductive P | e (v : V) | arr (i : Fin 3)
  deriving DecidableEq

/-- Each element of `P` as a path of the Mathlib quiver `K₃`. -/
def P.toPath : P → Σ a b : V, Quiver.Path a b
  | .e v => ⟨v, v, .nil⟩
  | .arr i => ⟨.one, .two, Quiver.Path.nil.cons (show V.one ⟶ V.two from i)⟩

/-- `P` lists every path of `K₃` exactly once. -/
theorem paths_bijective : Function.Bijective P.toPath := by
  constructor
  · rintro (v | i) (w | j) h
    · exact congrArg P.e (congrArg Sigma.fst h)
    · exact absurd (congrArg (fun s : Σ a b : V, Quiver.Path a b => s.2.2.length) h)
        (by simp [P.toPath])
    · exact absurd (congrArg (fun s : Σ a b : V, Quiver.Path a b => s.2.2.length) h)
        (by simp [P.toPath])
    · simp only [P.toPath, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact congrArg P.arr (eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons h))
  · rintro ⟨a, b, p⟩
    rcases path_shape p with h | ⟨rfl, rfl, h⟩
    · have hab := Quiver.Path.eq_of_length_zero p h
      subst hab
      exact ⟨.e a, by simp [P.toPath, (Quiver.Path.eq_nil_of_length_zero p h)]⟩
    · cases p with
      | cons q f =>
        rename_i c
        have hq : q.length = 0 := by simpa using h
        have := Quiver.Path.eq_of_length_zero q hq
        subst this
        rw [Quiver.Path.eq_nil_of_length_zero q hq]
        exact ⟨.arr f, rfl⟩

/-- Concatenation of paths of `K₃` (`none` when the paths are not composable or the
concatenation does not exist). -/
def concat : P → P → Option P
  | .e .one, .e .one => some (.e .one)
  | .e .two, .e .two => some (.e .two)
  | .e .one, .arr i => some (.arr i)
  | .arr i, .e .two => some (.arr i)
  | _, _ => none

variable (k : Type*) [Field k]

/-- The path algebra `kK₃`: `k`-linear combinations of the paths of `K₃`. -/
def PathAlg := P → k

instance : AddCommGroup (PathAlg k) := inferInstanceAs (AddCommGroup (P → k))
instance : Module k (PathAlg k) := inferInstanceAs (Module k (P → k))

variable {k}

/-- Product on `kK₃`, the bilinear extension of concatenation (see `basis_mul_basis`). -/
instance : Mul (PathAlg k) where
  mul x y := fun
    | .e .one => x (.e .one) * y (.e .one)
    | .e .two => x (.e .two) * y (.e .two)
    | .arr i => x (.e .one) * y (.arr i) + x (.arr i) * y (.e .two)

instance : One (PathAlg k) where
  one := fun
    | .e _ => 1
    | .arr _ => 0

@[simp] lemma mul_e1 (x y : PathAlg k) : (x * y) (.e .one) = x (.e .one) * y (.e .one) := rfl
@[simp] lemma mul_e2 (x y : PathAlg k) : (x * y) (.e .two) = x (.e .two) * y (.e .two) := rfl
@[simp] lemma mul_arr (x y : PathAlg k) (i : Fin 3) :
    (x * y) (.arr i) = x (.e .one) * y (.arr i) + x (.arr i) * y (.e .two) := rfl
@[simp] lemma one_e (v : V) : (1 : PathAlg k) (.e v) = 1 := rfl
@[simp] lemma one_arr (i : Fin 3) : (1 : PathAlg k) (.arr i) = 0 := rfl
@[simp] lemma add_apply' (x y : PathAlg k) (p : P) : (x + y) p = x p + y p := rfl
@[simp] lemma sub_apply' (x y : PathAlg k) (p : P) : (x - y) p = x p - y p := rfl
@[simp] lemma zero_apply' (p : P) : (0 : PathAlg k) p = 0 := rfl
@[simp] lemma smul_apply' (c : k) (x : PathAlg k) (p : P) : (c • x) p = c * x p := rfl

omit [Field k] in
lemma PathAlg.ext {x y : PathAlg k} (h : ∀ p, x p = y p) : x = y := funext h

omit [Field k] in
/-- Case split on the coordinates of an element of `kK₃`. -/
lemma PathAlg.ext' {x y : PathAlg k} (h1 : x (.e .one) = y (.e .one))
    (h2 : x (.e .two) = y (.e .two)) (h3 : ∀ i, x (.arr i) = y (.arr i)) : x = y :=
  PathAlg.ext fun | .e .one => h1 | .e .two => h2 | .arr i => h3 i

instance : Ring (PathAlg k) :=
  { (inferInstance : AddCommGroup (PathAlg k)) with
    mul_assoc := fun x y z => PathAlg.ext' (by simp; ring) (by simp; ring) (fun i => by simp; ring)
    one_mul := fun x => PathAlg.ext' (by simp) (by simp) (fun i => by simp)
    mul_one := fun x => PathAlg.ext' (by simp) (by simp) (fun i => by simp)
    left_distrib := fun x y z => PathAlg.ext' (by simp; ring) (by simp; ring) (fun i => by simp; ring)
    right_distrib := fun x y z =>
      PathAlg.ext' (by simp; ring) (by simp; ring) (fun i => by simp; ring)
    zero_mul := fun x => PathAlg.ext' (by simp) (by simp) (fun i => by simp)
    mul_zero := fun x => PathAlg.ext' (by simp) (by simp) (fun i => by simp) }

instance : Algebra k (PathAlg k) :=
  Algebra.ofModule
    (fun c x y => PathAlg.ext' (by simp; ring) (by simp; ring) (fun i => by simp; ring))
    (fun c x y => PathAlg.ext' (by simp; ring) (by simp; ring) (fun i => by simp; ring))

/-- The basis element of `kK₃` given by a path. -/
def basis (p : P) : PathAlg k := fun q => if q = p then 1 else 0

/-- The product of two basis paths is their concatenation, or `0` if it does not exist:
`kK₃` is the path algebra of `K₃`. -/
theorem basis_mul_basis (p q : P) :
    basis p * basis q = match concat p q with
      | some r => (basis r : PathAlg k)
      | none => 0 := by
  rcases p with (_ | _) | i <;> rcases q with (_ | _) | j <;>
    refine PathAlg.ext' ?_ ?_ (fun l => ?_) <;> simp [basis, concat]

/-! ## The derivations `D i j` and their classes in `HH¹` -/

/-- `D i j` sends the arrow `αⱼ` to `αᵢ` and kills `e₁, e₂` and the other arrows. -/
def Dfun (i j : Fin 3) (x : PathAlg k) : PathAlg k := fun
  | .e _ => 0
  | .arr l => if l = i then x (.arr j) else 0

@[simp] lemma Dfun_e (i j : Fin 3) (x : PathAlg k) (v : V) : Dfun i j x (.e v) = 0 := rfl
@[simp] lemma Dfun_arr (i j l : Fin 3) (x : PathAlg k) :
    Dfun i j x (.arr l) = if l = i then x (.arr j) else 0 := rfl

/-- `D i j` as a `k`-linear map. -/
def Dlin (i j : Fin 3) : Module.End k (PathAlg k) where
  toFun := Dfun i j
  map_add' x y := PathAlg.ext' (by simp) (by simp) (fun l => by simp; split_ifs <;> simp)
  map_smul' c x := PathAlg.ext' (by simp) (by simp) (fun l => by simp)

@[simp] lemma Dlin_apply (i j : Fin 3) (x : PathAlg k) : Dlin i j x = Dfun i j x := rfl

lemma Dlin_mem (i j : Fin 3) : Dlin i j ∈ Der k (PathAlg k) := by
  intro x y
  refine PathAlg.ext' (by simp) (by simp) (fun l => ?_)
  simp only [Dlin_apply, Dfun_arr, mul_arr, add_apply', Dfun_e]
  split_ifs <;> ring

/-- `D i j` as an element of the Lie algebra `Der(kK₃)`. -/
def D (i j : Fin 3) : Der k (PathAlg k) := ⟨Dlin i j, Dlin_mem i j⟩

lemma D_bracket {i j m : Fin 3} (hij : i ≠ j) :
    ⁅(D i m : Der k (PathAlg k)), D (k := k) m j⁆ = D i j := by
  apply Subtype.ext
  refine LinearMap.ext fun x => PathAlg.ext' (by simp [D, LieRing.of_associative_ring_bracket])
    (by simp [D, LieRing.of_associative_ring_bracket]) (fun l => ?_)
  simp only [D, LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket,
    LinearMap.sub_apply, Module.End.mul_apply, sub_apply', Dlin_apply, Dfun_arr]
  have : j ≠ i := Ne.symm hij
  split_ifs <;> simp_all

/-- No `D i j` with `i ≠ j` is inner. -/
lemma D_not_inner {i j : Fin 3} (hij : i ≠ j) : D i j ∉ Inn k (PathAlg k) := by
  rintro ⟨a, ha⟩
  have h := congrArg (fun f : Module.End k (PathAlg k) => f (basis (.arr j)) (.arr i)) ha
  simp [D, basis, hij] at h

/-- The class of `D i j` in `HH¹(kK₃)`. -/
def d (i j : Fin 3) : HH1 k (PathAlg k) := LieSubmodule.Quotient.mk (D i j)

lemma d_bracket {i j m : Fin 3} (hij : i ≠ j) :
    ⁅(d i m : HH1 k (PathAlg k)), d (k := k) m j⁆ = d i j := by
  rw [d, d, d, ← LieSubmodule.Quotient.mk_bracket, D_bracket hij]

lemma d_mem_derivedSeries (n : ℕ) :
    ∀ i j : Fin 3, i ≠ j → d i j ∈ derivedSeries k (HH1 k (PathAlg k)) n := by
  induction n with
  | zero => intro i j _; simp
  | succ n ih =>
    intro i j hij
    obtain ⟨m, hmi, hmj⟩ : ∃ m : Fin 3, m ≠ i ∧ m ≠ j := by revert i j; decide
    rw [← d_bracket (m := m) hij, derivedSeries_def, derivedSeriesOfIdeal_succ]
    exact LieSubmodule.lie_mem_lie (ih i m (Ne.symm hmi)) (ih m j hmj)

/-- Over every field `k`, `HH¹(kK₃)` is not solvable. -/
theorem HH1_not_solvable : ¬ LieAlgebra.IsSolvable (HH1 k (PathAlg k)) := by
  intro h
  obtain ⟨n, hn⟩ := (LieAlgebra.isSolvable_iff k (HH1 k (PathAlg k))).mp h
  have hmem := d_mem_derivedSeries (k := k) n 0 1 (by decide)
  rw [hn, LieSubmodule.mem_bot, d, LieSubmodule.Quotient.mk_eq_zero'] at hmem
  exact D_not_inner (by decide) hmem

/-- **Conjecture 00000004044 is false.** The generalized Kronecker quiver `K₃` (2 vertices,
3 parallel arrows) has all its oriented cycles broken after removing at most one vertex (it has
none), but over every field `k` the Lie algebra `HH¹(kK₃) = Der/Inn` of its path algebra is not
solvable. -/
theorem conjecture_00000004044_false :
    CyclesBrokenByAtMostOneVertex V ∧ ¬ LieAlgebra.IsSolvable (HH1 k (PathAlg k)) :=
  ⟨K3_cyclesBroken, HH1_not_solvable⟩

/-- The conjectured equivalence fails for `kK₃`. -/
theorem conjecture_00000004044_iff_fails :
    ¬ (LieAlgebra.IsSolvable (HH1 k (PathAlg k)) ↔ CyclesBrokenByAtMostOneVertex V) :=
  fun h => HH1_not_solvable (h.mpr K3_cyclesBroken)

end C4044
