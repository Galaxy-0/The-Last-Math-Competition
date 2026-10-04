/-!
# Conjecture 00000000297: there is no aperiodic set of two Wang tiles

The conjecture claims that there is an aperiodic rotation-free set of only
2 Wang tiles, that no single Wang tile is aperiodic, and hence that the
minimal size of a rotation-free aperiodic Wang tile set is exactly 2.

We prove that **every set of at most 2 Wang tiles that tiles the plane also
has a doubly periodic tiling** (with periods `(2,0)` and `(0,2)`).  So no
set of at most 2 Wang tiles is aperiodic, under either the strong reading
(no tiling has any nonzero period) or the weak reading (no tiling has two
independent periods).  The first clause of the conjecture, and with it the
claim "the minimum is exactly 2", is false.  (The second clause, that a
single tile is never aperiodic, is true and is proved here as well.)

Wang tiles are formalized from scratch: a tile is a quadruple of edge colors
`(n, e, s, w)` taken from an arbitrary color type `C`, tiles are never
rotated, and a tiling of `ℤ²` assigns a tile of the set to every cell so that
the east color of each tile equals the west color of its right neighbour and
the north color equals the south color of its upper neighbour.
-/

namespace Wang

/-- A Wang tile: north, east, south and west edge colors, from any color type `C`. -/
structure Tile (C : Type) where
  n : C
  e : C
  s : C
  w : C
deriving DecidableEq

variable {C : Type}

/-- `b` may be placed immediately to the right of `a`. -/
def HMatch (a b : Tile C) : Prop := a.e = b.w

/-- `b` may be placed immediately above `a`. -/
def VMatch (a b : Tile C) : Prop := a.n = b.s

/-- `f` is a tiling of the plane `ℤ²` by the tile set `T` (tiles are not rotated):
every cell `(x, y)` carries a tile of `T`, and all shared edges have equal colors. -/
def IsTiling (T : List (Tile C)) (f : Int → Int → Tile C) : Prop :=
  ∀ x y : Int, f x y ∈ T ∧ HMatch (f x y) (f (x + 1) y) ∧ VMatch (f x y) (f x (y + 1))

/-- The tile set `T` tiles the plane. -/
def Tiles (T : List (Tile C)) : Prop := ∃ f, IsTiling T f

/-- `(a, b)` is a period of `f`. -/
def IsPeriod (f : Int → Int → Tile C) (a b : Int) : Prop := ∀ x y, f (x + a) (y + b) = f x y

/-- `f` has some nonzero period. -/
def IsPeriodic (f : Int → Int → Tile C) : Prop :=
  ∃ a b : Int, (a ≠ 0 ∨ b ≠ 0) ∧ IsPeriod f a b

/-- `f` has two linearly independent periods. -/
def IsDoublyPeriodic (f : Int → Int → Tile C) : Prop :=
  ∃ a b c d : Int, a * d - b * c ≠ 0 ∧ IsPeriod f a b ∧ IsPeriod f c d

/-- (Strongly) aperiodic tile set: it tiles the plane, but no tiling has a nonzero period.
This is the standard definition for Wang tiles. -/
def Aperiodic (T : List (Tile C)) : Prop :=
  Tiles T ∧ ∀ f, IsTiling T f → ¬ IsPeriodic f

/-- Weakly aperiodic tile set: it tiles the plane, but no tiling is doubly periodic. -/
def WeaklyAperiodic (T : List (Tile C)) : Prop :=
  Tiles T ∧ ∀ f, IsTiling T f → ¬ IsDoublyPeriodic f

/-- A strongly aperiodic set is weakly aperiodic. -/
theorem Aperiodic.weakly {T : List (Tile C)} (h : Aperiodic T) : WeaklyAperiodic T := by
  refine ⟨h.1, fun f hf ⟨a, b, c, d, hdet, hab, _⟩ => h.2 f hf ⟨a, b, ?_, hab⟩⟩
  by_cases ha : a = 0
  · subst ha
    by_cases hb : b = 0
    · subst hb; simp at hdet
    · exact Or.inr hb
  · exact Or.inl ha

/-! ## The local lemma

If two tiles `t0, t1` do not match horizontally in both orders, then in any tiling
by `{t0, t1}` every tile matches itself horizontally.  Indeed, if the tile `b` at
`(x, y)` did not match itself, its left neighbour `a` and right neighbour `c` would
both be the other tile, and then `a | b` and `b | c` give both cross matches. -/

theorem hloop {t0 t1 : Tile C} {f : Int → Int → Tile C} (hf : IsTiling [t0, t1] f)
    (hA : ¬ (HMatch t0 t1 ∧ HMatch t1 t0)) (x y : Int) : HMatch (f x y) (f x y) := by
  refine Classical.byContradiction fun h => ?_
  obtain ⟨ma, hab, -⟩ := hf (x - 1) y
  rw [Int.sub_add_cancel] at hab
  obtain ⟨mb, hbc, -⟩ := hf x y
  have mc := (hf (x + 1) y).1
  generalize f (x - 1) y = a at *
  generalize f x y = b at *
  generalize f (x + 1) y = c at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ma mb mc
  rcases ma with rfl | rfl <;> rcases mb with rfl | rfl <;> rcases mc with rfl | rfl <;>
    first
    | exact h hab
    | exact h hbc
    | exact hA ⟨hab, hbc⟩
    | exact hA ⟨hbc, hab⟩

/-- The vertical version of `hloop`. -/
theorem vloop {t0 t1 : Tile C} {f : Int → Int → Tile C} (hf : IsTiling [t0, t1] f)
    (hA : ¬ (VMatch t0 t1 ∧ VMatch t1 t0)) (x y : Int) : VMatch (f x y) (f x y) := by
  refine Classical.byContradiction fun h => ?_
  obtain ⟨ma, -, hab⟩ := hf x (y - 1)
  rw [Int.sub_add_cancel] at hab
  obtain ⟨mb, -, hbc⟩ := hf x y
  have mc := (hf x (y + 1)).1
  generalize f x (y - 1) = a at *
  generalize f x y = b at *
  generalize f x (y + 1) = c at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ma mb mc
  rcases ma with rfl | rfl <;> rcases mb with rfl | rfl <;> rcases mc with rfl | rfl <;>
    first
    | exact h hab
    | exact h hbc
    | exact hA ⟨hab, hbc⟩
    | exact hA ⟨hbc, hab⟩

/-! ## Four doubly periodic patterns -/

/-- The patterns used below: constant, checkerboard, constant rows, constant columns. -/
def constPat (t : Tile C) : Int → Int → Tile C := fun _ _ => t
def checker (t0 t1 : Tile C) : Int → Int → Tile C :=
  fun x y => if (x + y) % 2 = 0 then t0 else t1
def stripesH (t0 t1 : Tile C) : Int → Int → Tile C :=
  fun _ y => if y % 2 = 0 then t0 else t1
def stripesV (t0 t1 : Tile C) : Int → Int → Tile C :=
  fun x _ => if x % 2 = 0 then t0 else t1

/-- Periods `(2,0)` and `(0,2)`. -/
def Period22 (g : Int → Int → Tile C) : Prop := ∀ x y, g (x + 2) y = g x y ∧ g x (y + 2) = g x y

theorem const_p22 (t : Tile C) : Period22 (constPat t) := fun _ _ => ⟨rfl, rfl⟩

theorem checker_p22 (t0 t1 : Tile C) : Period22 (checker t0 t1) := by
  intro x y
  have h1 : (x + 2 + y) % 2 = (x + y) % 2 := by omega
  have h2 : (x + (y + 2)) % 2 = (x + y) % 2 := by omega
  simp [checker, h1, h2]

theorem stripesH_p22 (t0 t1 : Tile C) : Period22 (stripesH t0 t1) := by
  intro x y
  have h2 : (y + 2) % 2 = y % 2 := by omega
  simp [stripesH, h2]

theorem stripesV_p22 (t0 t1 : Tile C) : Period22 (stripesV t0 t1) := by
  intro x y
  have h1 : (x + 2) % 2 = x % 2 := by omega
  simp [stripesV, h1]

theorem const_tiling {T : List (Tile C)} {t : Tile C} (hm : t ∈ T) (hh : HMatch t t)
    (hv : VMatch t t) : IsTiling T (constPat t) := fun _ _ => ⟨hm, hh, hv⟩

theorem checker_tiling (t0 t1 : Tile C) (hH : HMatch t0 t1 ∧ HMatch t1 t0)
    (hV : VMatch t0 t1 ∧ VMatch t1 t0) : IsTiling [t0, t1] (checker t0 t1) := by
  intro x y
  have e1 : (x + 1 + y) % 2 = 0 ↔ ¬ (x + y) % 2 = 0 := by omega
  have e2 : (x + (y + 1)) % 2 = 0 ↔ ¬ (x + y) % 2 = 0 := by omega
  simp only [checker, e1, e2]
  by_cases h : (x + y) % 2 = 0
  · simp [h, hH.1, hV.1]
  · simp [h, hH.2, hV.2]

theorem stripesH_tiling (t0 t1 : Tile C) (hH : HMatch t0 t0 ∧ HMatch t1 t1)
    (hV : VMatch t0 t1 ∧ VMatch t1 t0) : IsTiling [t0, t1] (stripesH t0 t1) := by
  intro x y
  have e2 : (y + 1) % 2 = 0 ↔ ¬ y % 2 = 0 := by omega
  simp only [stripesH, e2]
  by_cases h : y % 2 = 0
  · simp [h, hH.1, hV.1]
  · simp [h, hH.2, hV.2]

theorem stripesV_tiling (t0 t1 : Tile C) (hH : HMatch t0 t1 ∧ HMatch t1 t0)
    (hV : VMatch t0 t0 ∧ VMatch t1 t1) : IsTiling [t0, t1] (stripesV t0 t1) := by
  intro x y
  have e1 : (x + 1) % 2 = 0 ↔ ¬ x % 2 = 0 := by omega
  simp only [stripesV, e1]
  by_cases h : x % 2 = 0
  · simp [h, hH.1, hV.1]
  · simp [h, hH.2, hV.2]

/-! ## Main theorem for two tiles -/

/-- If two distinct members of `{t0, t1}` both satisfy a property, then `t0` and `t1` do. -/
theorem both_of_ne {t0 t1 a b : Tile C} {P : Tile C → Prop} (ma : a ∈ [t0, t1])
    (mb : b ∈ [t0, t1]) (hne : b ≠ a) (pa : P a) (pb : P b) : P t0 ∧ P t1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ma mb
  rcases ma with rfl | rfl <;> rcases mb with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨pa, pb⟩
  · exact ⟨pb, pa⟩
  · exact absurd rfl hne

/-- **Key theorem.** If `{t0, t1}` tiles the plane, it has a tiling with periods
`(2,0)` and `(0,2)`. -/
theorem two_tiles_periodic (t0 t1 : Tile C) (h : Tiles [t0, t1]) :
    ∃ g, IsTiling [t0, t1] g ∧ Period22 g := by
  obtain ⟨f, hf⟩ := h
  by_cases hH : HMatch t0 t1 ∧ HMatch t1 t0 <;> by_cases hV : VMatch t0 t1 ∧ VMatch t1 t0
  · -- both cross matches in both directions: checkerboard
    exact ⟨_, checker_tiling t0 t1 hH hV, checker_p22 t0 t1⟩
  · -- every tile matches itself vertically
    by_cases e : f 1 0 = f 0 0
    · refine ⟨_, const_tiling (hf 0 0).1 ?_ (vloop hf hV 0 0), const_p22 _⟩
      have := (hf 0 0).2.1
      rwa [Int.zero_add, e] at this
    · have hv := both_of_ne (P := fun t => VMatch t t) (hf 0 0).1 (hf 1 0).1 e
        (vloop hf hV 0 0) (vloop hf hV 1 0)
      exact ⟨_, stripesV_tiling t0 t1 hH hv, stripesV_p22 t0 t1⟩
  · -- every tile matches itself horizontally
    by_cases e : f 0 1 = f 0 0
    · refine ⟨_, const_tiling (hf 0 0).1 (hloop hf hH 0 0) ?_, const_p22 _⟩
      have := (hf 0 0).2.2
      rwa [Int.zero_add, e] at this
    · have hh := both_of_ne (P := fun t => HMatch t t) (hf 0 0).1 (hf 0 1).1 e
        (hloop hf hH 0 0) (hloop hf hH 0 1)
      exact ⟨_, stripesH_tiling t0 t1 hh hV, stripesH_p22 t0 t1⟩
  · -- every tile matches itself in both directions: constant tiling
    exact ⟨_, const_tiling (hf 0 0).1 (hloop hf hH 0 0) (vloop hf hV 0 0), const_p22 _⟩

/-! ## From periods `(2,0), (0,2)` to periodicity -/

theorem p22_period_20 {g : Int → Int → Tile C} (h : Period22 g) : IsPeriod g 2 0 := by
  intro x y; rw [Int.add_zero]; exact (h x y).1

theorem p22_period_02 {g : Int → Int → Tile C} (h : Period22 g) : IsPeriod g 0 2 := by
  intro x y; rw [Int.add_zero]; exact (h x y).2

theorem p22_periodic {g : Int → Int → Tile C} (h : Period22 g) : IsPeriodic g :=
  ⟨2, 0, Or.inl (by decide), p22_period_20 h⟩

theorem p22_doubly {g : Int → Int → Tile C} (h : Period22 g) : IsDoublyPeriodic g :=
  ⟨2, 0, 0, 2, by decide, p22_period_20 h, p22_period_02 h⟩

theorem IsTiling.mono {T T' : List (Tile C)} {f : Int → Int → Tile C}
    (hT : ∀ t, t ∈ T → t ∈ T') (hf : IsTiling T f) : IsTiling T' f :=
  fun x y => ⟨hT _ (hf x y).1, (hf x y).2⟩

/-- **Every tile set with at most two tiles that tiles the plane has a tiling with periods
`(2,0)` and `(0,2)`** (in particular a doubly periodic one, and one with a nonzero period).
Duplicates in the list are allowed; the 0-, 1- and 2-tile cases are all covered. -/
theorem le_two_tiles_periodic (T : List (Tile C)) (hlen : T.length ≤ 2) (h : Tiles T) :
    ∃ g, IsTiling T g ∧ Period22 g ∧ IsPeriodic g ∧ IsDoublyPeriodic g := by
  match T, hlen, h with
  | [], _, ⟨f, hf⟩ =>
    have h0 := (hf 0 0).1
    simp at h0
  | [a], _, ⟨f, hf⟩ =>
    have hf' : IsTiling [a, a] f := hf.mono (by intro t ht; simp_all)
    obtain ⟨g, hg, hp⟩ := two_tiles_periodic a a ⟨f, hf'⟩
    exact ⟨g, hg.mono (by intro t ht; simp_all), hp, p22_periodic hp, p22_doubly hp⟩
  | [a, b], _, h =>
    obtain ⟨g, hg, hp⟩ := two_tiles_periodic a b h
    exact ⟨g, hg, hp, p22_periodic hp, p22_doubly hp⟩
  | _ :: _ :: _ :: _, hlen, _ => simp at hlen

/-- No tile set with at most two tiles is weakly aperiodic. -/
theorem not_weaklyAperiodic (T : List (Tile C)) (hlen : T.length ≤ 2) :
    ¬ WeaklyAperiodic T := by
  intro ⟨ht, hno⟩
  obtain ⟨g, hg, -, -, hd⟩ := le_two_tiles_periodic T hlen ht
  exact hno g hg hd

/-- No tile set with at most two tiles is (strongly) aperiodic. -/
theorem not_aperiodic (T : List (Tile C)) (hlen : T.length ≤ 2) : ¬ Aperiodic T :=
  fun h => not_weaklyAperiodic T hlen h.weakly

/-! ## The conjecture -/

/-- Clause 1: there is an aperiodic (rotation-free) set of only 2 Wang tiles. -/
def Clause1 (C : Type) : Prop := ∃ T : List (Tile C), T.length = 2 ∧ Aperiodic T

/-- Clause 2: no single (rotation-free) Wang tile is aperiodic. -/
def Clause2 (C : Type) : Prop := ¬ ∃ t : Tile C, Aperiodic [t]

/-- "The minimal size of a rotation-free aperiodic Wang tile set is exactly `k`". -/
def MinAperiodicSize (C : Type) (k : Nat) : Prop :=
  (∃ T : List (Tile C), T.length = k ∧ Aperiodic T) ∧
    ∀ T : List (Tile C), T.length < k → ¬ Aperiodic T

/-- The full conjecture, as stated. -/
def Conjecture297 (C : Type) : Prop := Clause1 C ∧ Clause2 C ∧ MinAperiodicSize C 2

/-- **Clause 1 is false**, for every color type. -/
theorem clause1_false (C : Type) : ¬ Clause1 C :=
  fun ⟨T, hlen, hT⟩ => not_aperiodic T (by omega) hT

/-- Clause 1 is false even with "aperiodic" weakened to "weakly aperiodic". -/
theorem clause1_weak_false (C : Type) :
    ¬ ∃ T : List (Tile C), T.length = 2 ∧ WeaklyAperiodic T :=
  fun ⟨T, hlen, hT⟩ => not_weaklyAperiodic T (by omega) hT

/-- Clause 1 is false even with "only 2" read as "at most 2". -/
theorem clause1_le_false (C : Type) :
    ¬ ∃ T : List (Tile C), T.length ≤ 2 ∧ WeaklyAperiodic T :=
  fun ⟨T, hlen, hT⟩ => not_weaklyAperiodic T hlen hT

/-- Clause 2 is true (it is not what fails). -/
theorem clause2_true (C : Type) : Clause2 C :=
  fun ⟨t, ht⟩ => not_aperiodic [t] (by simp) ht

/-- The minimal aperiodic size is not 2. -/
theorem minSize_ne_two (C : Type) : ¬ MinAperiodicSize C 2 :=
  fun ⟨h, _⟩ => clause1_false C h

/-- **Conjecture 00000000297 is false** (for every color type `C`). -/
theorem conjecture_00000000297_false (C : Type) : ¬ Conjecture297 C :=
  fun ⟨h, _, _⟩ => clause1_false C h

/-! ## Non-vacuity checks (with natural-number colors) -/

/-- A 2-tile set that tiles the plane (so `Tiles` is satisfiable for 2-tile sets) ... -/
theorem tiles_example : Tiles [(⟨0, 1, 0, 0⟩ : Tile Nat), ⟨0, 0, 0, 1⟩] :=
  ⟨stripesV ⟨0, 1, 0, 0⟩ ⟨0, 0, 0, 1⟩,
    stripesV_tiling _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩⟩

/-- ... and a 2-tile set that does not (so `Tiles` is not trivially true). -/
theorem not_tiles_example : ¬ Tiles [(⟨0, 0, 0, 1⟩ : Tile Nat), ⟨0, 2, 0, 1⟩] := by
  intro ⟨f, hf⟩
  obtain ⟨m0, h, -⟩ := hf 0 0
  have m1 := (hf 1 0).1
  rw [Int.zero_add] at h
  generalize f 0 0 = a at *
  generalize f 1 0 = b at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at m0 m1
  rcases m0 with rfl | rfl <;> rcases m1 with rfl | rfl <;> simp [HMatch] at h

/-- A four-tile set (blank, horizontal line, vertical line, cross) ... -/
def blank : Tile Nat := ⟨0, 0, 0, 0⟩
def hline : Tile Nat := ⟨0, 1, 0, 1⟩
def vline : Tile Nat := ⟨2, 0, 2, 0⟩
def cross : Tile Nat := ⟨2, 1, 2, 1⟩

/-- ... and its tiling with a single cross at the origin. -/
def crossTiling : Int → Int → Tile Nat := fun x y =>
  if x = 0 ∧ y = 0 then cross else if y = 0 then hline else if x = 0 then vline else blank

theorem crossTiling_isTiling : IsTiling [blank, hline, vline, cross] crossTiling := by
  intro x y
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hx1 : x + 1 = 0 <;>
    by_cases hy1 : y + 1 = 0 <;>
    simp_all [crossTiling, HMatch, VMatch, blank, hline, vline, cross]

/-- This tiling has no nonzero period, so `IsPeriodic` is not trivially true of tilings
(the theorem above produces *a* periodic tiling, it does not say every tiling is periodic). -/
theorem crossTiling_not_periodic : ¬ IsPeriodic crossTiling := by
  intro ⟨a, b, hab, hp⟩
  have h := hp (-a) (-b)
  rw [Int.add_left_neg, Int.add_left_neg] at h
  by_cases ha : -a = 0 <;> by_cases hb : -b = 0
  · omega
  all_goals simp [crossTiling, ha, hb, cross, hline, vline, blank] at h

end Wang

#print axioms Wang.two_tiles_periodic
#print axioms Wang.le_two_tiles_periodic
#print axioms Wang.clause1_false
#print axioms Wang.clause1_le_false
#print axioms Wang.clause2_true
#print axioms Wang.conjecture_00000000297_false
#print axioms Wang.crossTiling_not_periodic
