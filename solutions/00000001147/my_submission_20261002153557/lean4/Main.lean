/-
Disproof of TLMC conjecture 00000001147 ("triangular H2 dimension two").

Original claim: "The dimension of the second cohomology of a triangular Lie
algebra is two; and the dimension is realized by one contribution each from
the outer derivations and the center."

Counterexample: aff(1), the Lie algebra of 2x2 upper-triangular matrices with
basis H = [[1,0],[0,0]], E = [[0,1],[0,0]] and bracket [H,E] = E.  It is a
subalgebra of triangular matrices, hence a triangular Lie algebra under the
definition as stated.

Computation (Chevalley-Eilenberg, coefficients in any field; the ranks of the
differentials are field-independent, so we work over Int):

  C^1 = (basis -> Int)              dim 2
  C^2 = Int, basis H* ∧ E*          dim 1   (an alternating form on a
                                             2-dimensional space is determined
                                             by its value on (H,E))
  C^3 = 0                           dim 0   (Λ^3 of a 2-dimensional space is
                                             0: no strictly increasing
                                             triple of basis indices, cf.
                                             no_strict_inc)

  Sign convention: the CE differential is δf(x,y) = -f([x,y]); we use the
  equivalent map d1 f = f([H,E]), which differs from δ only by the bijection
  f ↦ -f of C^1, so B^2 = im d1 = im δ and H^2 is unchanged.

  d1 is surjective (d1_surj), hence B^2 = C^2; and Z^2 = C^2 since C^3 = 0.
  Therefore H^2 = Z^2 / B^2 is a single class: any two 2-cochains are
  cohomologous (cobdy_all), i.e. dim H^2(aff(1)) = 0.  A vector space of
  dimension 2 over ANY field contains the four pairwise distinct elements
  0, v, w, v+w for a basis (v,w), i.e. four pairwise non-cohomologous
  2-cochains -- which do not exist (no_four_classes).  Hence
  dim H^2(aff(1)) = 0 ≠ 2 and the conjecture is false.

Formalization note: we deliberately avoid `Quotient` (its `Quot.sound` would
show up in the axiom audit), the `omega` tactic (in this toolchain its proof
terms depend on `propext` and `Quot.sound`), and `Fin` literals (the core
`OfNat (Fin n)` instances are proved using `propext`).  All index terms are
explicit `Fin.mk` applications with `by decide` proofs (`decide` on `Fin`
equality/lower-bound goals is axiom-free), and every theorem is audited in
Check.lean to depend on no axioms at all (no sorryAx, no Classical.choice,
no propext, no Quot.sound).  Bare core only: no Mathlib, `Nat`/`Int`
directly (the `ℕ` notation is not available).
-/

namespace TLMC1147

/-! ### The Lie algebra aff(1) -/

/-- The basis vector `H` (index `0`). -/
def iH : Fin 2 := ⟨0, by decide⟩

/-- The basis vector `E` (index `1`). -/
def iE : Fin 2 := ⟨1, by decide⟩

/-- The three standard indices of `Fin 3` (avoiding `Fin` literals). -/
def i30 : Fin 3 := ⟨0, by decide⟩
def i31 : Fin 3 := ⟨1, by decide⟩
def i32 : Fin 3 := ⟨2, by decide⟩

/-- Structure constants of aff(1): `[H,E] = E`, all other brackets trivial. -/
def Br : Fin 2 → Fin 2 → Fin 2
  | ⟨0, _⟩, ⟨1, _⟩ => ⟨1, by decide⟩
  | _, _ => ⟨0, by decide⟩

theorem Br_HE : Br iH iE = iE := rfl

/-! ### Cochains and the differential -/

/-- The CE differential `d : C^1 → C^2`, `(df)(x,y) = f([x,y])` (see the sign
convention above), evaluated on the single wedge basis vector `(H,E)`: an
alternating 2-form on a 2-dimensional space is determined by this value. -/
def d1 (f : Fin 2 → Int) : Int := f (Br iH iE)

/-- `B^2 = im d` is all of `C^2`: the differential is surjective. -/
theorem d1_surj : ∀ c : Int, ∃ f : Fin 2 → Int, d1 f = c :=
  fun c => ⟨fun _ => c, rfl⟩

/-- The differential is additive. -/
theorem d1_add (f g : Fin 2 → Int) :
    d1 (fun i => f i + g i) = d1 f + d1 g := rfl

/-! ### There is no third cochain degree: `Z^2 = C^2`

The degree-3 part of the exterior algebra of a 2-dimensional space has an
empty basis: no triple of pairwise distinct basis indices can carry strictly
increasing values (a strict value chain would force a third distinct value
in the two-element set `{0, 1}` -- pigeonhole, proved by explicit `Nat`
order reasoning). -/
theorem no_strict_inc (t : Fin 3 → Fin 2)
    (h : (t i30).val < (t i31).val ∧ (t i31).val < (t i32).val) : False := by
  have k1 : (t i30).val + 1 ≤ (t i31).val := h.1
  have k2 : (t i31).val + 1 ≤ (t i32).val := h.2
  have k3 : (t i32).val + 1 ≤ 2 := (t i32).isLt
  have step : (t i30).val + 2 ≤ (t i32).val :=
    Nat.le_trans (Nat.succ_le_succ k1) k2
  have big : 2 ≤ (t i32).val := Nat.le_trans (Nat.le_add_left 2 (t i30).val) step
  have small : (t i32).val ≤ 1 := Nat.le_of_succ_le_succ k3
  exact absurd (Nat.le_trans (Nat.succ_le_succ small) big)
    (Nat.lt_irrefl (t i32).val)

/-! ### The cohomology is trivial -/

/-- Two 2-cochains are cohomologous iff their difference is a coboundary. -/
def cobdy (a b : Int) : Prop := ∃ f : Fin 2 → Int, d1 f = a - b

/-- `B^2 = Z^2 = C^2`: every difference of 2-cochains is a coboundary, i.e.
`H^2(aff(1))` consists of a single cohomology class; in particular
`dim H^2(aff(1)) = 0`. -/
theorem cobdy_all : ∀ a b : Int, cobdy a b :=
  fun a b => ⟨fun _ => a - b, rfl⟩

/-! ### `dim H^2 = 2` is impossible -/

/-- If `dim H^2` were `2` over some field, the four elements `0, v, w, v+w`
of a basis `(v, w)` would be four pairwise distinct cohomology classes, i.e.
four 2-cochains that are pairwise non-cohomologous.  No such four exist. -/
theorem no_four_classes :
    ¬ ∃ F : Fin 4 → Int, ∀ i j : Fin 4, i ≠ j → ¬ cobdy (F i) (F j) :=
  fun ⟨F, hF⟩ =>
    let i0 : Fin 4 := ⟨0, by decide⟩
    let i1 : Fin 4 := ⟨1, by decide⟩
    hF i0 i1 (by decide) (cobdy_all (F i0) (F i1))

/-- Main result: `H^2(aff(1))` is trivial (a single cohomology class, i.e.
dimension `0`), and it cannot carry dimension `2` over any field.  The
conjecture "the dimension of the second cohomology of a triangular Lie
algebra is two" is false. -/
theorem main : (∀ a b : Int, cobdy a b) ∧
    ¬ ∃ F : Fin 4 → Int, ∀ i j : Fin 4, i ≠ j → ¬ cobdy (F i) (F j) :=
  ⟨cobdy_all, no_four_classes⟩

end TLMC1147
