/-!
# Conjecture 00000007709: a convex rep-tile of order 5

The conjecture says, among other things:

> The order `k` of a convex rep-tile must be a perfect square or `k = 2`.

A polygon is a *rep-`k` tile* if it can be dissected into `k` pieces that are similar
to it and congruent to each other. We show that the right triangle with legs in ratio
`1 : 2` is a rep-5 tile. Since `5` is not a perfect square and `5 ≠ 2`, the clause fails.

Concretely, the triangle `T = ABC` with `A = (0,0)`, `B = (10,0)`, `C = (0,5)` is the union
of the five triangles

* `piece1 = A D C`,    `piece2 = A M3 M1`,  `piece3 = M3 B M2`,
* `piece4 = M1 M2 D`,  `piece5 = M3 M2 M1`,

where `D = (2,4)`, `M1 = (1,2)`, `M2 = (6,2)` and `M3 = (5,0)`. Piece `i` is the image of `T`
under the similarity `fᵢ(z) = (aᵢ·z̄ + bᵢ)/5` with `|aᵢ|² = 5`, which scales every
distance by `1/√5`.

## Model

* The plane is the rational plane `ℚ²`. A point is a homogeneous integer triple
  `(x, y, w)` with `w > 0` that stands for `(x/w, y/w)`. Every rational point has such a
  representation. Two triples are the same point (`Pt.same`) when `x·w' = x'·w` and
  `y·w' = y'·w`. All predicates below are invariant under this equivalence.
* `orient A B P` is the 3×3 determinant of the homogeneous coordinates. Its sign is the
  sign of the cross product `(B - A) × (P - A)`, because all `w` are positive.
* A convex polygon is a counterclockwise vertex list in which every vertex that is not
  an endpoint of an edge lies strictly to the left of that edge. Its closed region
  (`InPoly`) is the set of points on or to the left of every edge line. Its interior
  (`InPolyInt`) is the set of points strictly to the left of every edge line.
* `IsSimilarity f n m` says that `f` multiplies every squared distance by `n/m`.
* `RepTile vs k` asks for a list of `k` maps, each a similarity with squared ratio `1/k`
  (so the pieces are similar to the tile and congruent to each other), such that:
  - every image of the tile lies in the tile;
  - every point of the tile lies in some image;
  - the images of the interior are pairwise disjoint.

The only computations are linear-arithmetic goals over `Int` (closed by `omega`) and a few
finite `decide` checks.
-/

namespace RepTile5

/-! ## 1. The rational plane -/

/-- A point of `ℚ²` in homogeneous integer coordinates: `(x/w, y/w)` with `w > 0`. -/
structure Pt where
  x : Int
  y : Int
  w : Int
  hw : 0 < w

/-- Two homogeneous triples represent the same rational point. -/
def Pt.same (P Q : Pt) : Prop := P.x * Q.w = Q.x * P.w ∧ P.y * Q.w = Q.y * P.w

instance (P Q : Pt) : Decidable (P.same Q) := by unfold Pt.same; infer_instance

/-- The homogeneous linear form `a·x + b·y + c·w`. -/
def lf (a b c : Int) (P : Pt) : Int := a * P.x + b * P.y + c * P.w

theorem lf_cross (a b c : Int) {P Q : Pt} (h : P.same Q) :
    lf a b c P * Q.w = lf a b c Q * P.w := by
  obtain ⟨hx, hy⟩ := h
  unfold lf
  have e1 : (a * P.x + b * P.y + c * P.w) * Q.w
      = a * (P.x * Q.w) + b * (P.y * Q.w) + c * (P.w * Q.w) := by
    simp only [Int.add_mul, Int.mul_assoc]
  have e2 : (a * Q.x + b * Q.y + c * Q.w) * P.w
      = a * (Q.x * P.w) + b * (Q.y * P.w) + c * (P.w * Q.w) := by
    simp only [Int.add_mul, Int.mul_assoc, Int.mul_comm Q.w P.w]
  rw [e1, e2, hx, hy]

/-- Strict signs of homogeneous linear forms do not depend on the representative. -/
theorem lf_pos {a b c : Int} {P Q : Pt} (h : P.same Q) (hp : 0 < lf a b c P) :
    0 < lf a b c Q := by
  have e := lf_cross a b c h
  have h1 : 0 < lf a b c P * Q.w := Int.mul_pos hp Q.hw
  rw [e] at h1
  by_cases h2 : 0 < lf a b c Q
  · exact h2
  · have := Int.mul_nonpos_of_nonpos_of_nonneg (show lf a b c Q ≤ 0 by omega)
      (Int.le_of_lt P.hw)
    omega

/-- Non-strict signs of homogeneous linear forms do not depend on the representative. -/
theorem lf_nonneg {a b c : Int} {P Q : Pt} (h : P.same Q) (hp : 0 ≤ lf a b c P) :
    0 ≤ lf a b c Q := by
  have e := lf_cross a b c h
  have h1 : 0 ≤ lf a b c P * Q.w := Int.mul_nonneg hp (Int.le_of_lt Q.hw)
  rw [e] at h1
  by_cases h2 : 0 ≤ lf a b c Q
  · exact h2
  · have := Int.mul_neg_of_neg_of_pos (show lf a b c Q < 0 by omega) P.hw
    omega

/-- A triple and a positive multiple of it are the same point. -/
theorem same_of_scale (R P : Pt) (c : Int) (hx : R.x = c * P.x) (hy : R.y = c * P.y)
    (hw : R.w = c * P.w) : R.same P := by
  unfold Pt.same
  rw [hx, hy, hw]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  exact ⟨trivial, trivial⟩

/-! ## 2. Squared distances and similarities -/

/-- Numerator of the squared distance: `|PQ|² = sqNum P Q / sqDen P Q`. -/
def sqNum (P Q : Pt) : Int :=
  (P.x * Q.w - Q.x * P.w) * (P.x * Q.w - Q.x * P.w)
    + (P.y * Q.w - Q.y * P.w) * (P.y * Q.w - Q.y * P.w)

/-- Denominator of the squared distance. -/
def sqDen (P Q : Pt) : Int := (P.w * Q.w) * (P.w * Q.w)

/-- `f` multiplies every squared distance by `n / m` (`n, m > 0`). That is,
`|f P f Q|² = (n/m)·|P Q|²`, written without division. -/
def IsSimilarity (f : Pt → Pt) (n m : Int) : Prop :=
  0 < n ∧ 0 < m ∧ ∀ P Q : Pt, m * sqNum (f P) (f Q) * sqDen P Q = n * sqNum P Q * sqDen (f P) (f Q)

theorem sq_nonneg' (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -a := by omega
    have := Int.mul_nonneg h' h'
    rwa [Int.neg_mul_neg] at this

/-- A similarity is a well-defined map of rational points: it respects `Pt.same`. -/
theorem IsSimilarity.respects {f : Pt → Pt} {n m : Int} (hf : IsSimilarity f n m)
    {P Q : Pt} (h : P.same Q) : (f P).same (f Q) := by
  obtain ⟨_, hm, hfPQ⟩ := hf
  have h0 : sqNum P Q = 0 := by
    obtain ⟨hx, hy⟩ := h
    simp only [sqNum, hx, hy, Int.sub_self, Int.mul_zero, Int.add_zero]
  have hD : 0 < sqDen P Q := Int.mul_pos (Int.mul_pos P.hw Q.hw) (Int.mul_pos P.hw Q.hw)
  have e := hfPQ P Q
  rw [h0, Int.mul_zero, Int.zero_mul] at e
  have e2 : sqNum (f P) (f Q) = 0 := by
    rcases Int.mul_eq_zero.mp e with e3 | e3
    · rcases Int.mul_eq_zero.mp e3 with e4 | e4
      · omega
      · exact e4
    · omega
  unfold sqNum at e2
  have s1 := sq_nonneg' ((f P).x * (f Q).w - (f Q).x * (f P).w)
  have s2 := sq_nonneg' ((f P).y * (f Q).w - (f Q).y * (f P).w)
  have z1 : ((f P).x * (f Q).w - (f Q).x * (f P).w) * ((f P).x * (f Q).w - (f Q).x * (f P).w) = 0 := by
    omega
  have z2 : ((f P).y * (f Q).w - (f Q).y * (f P).w) * ((f P).y * (f Q).w - (f Q).y * (f P).w) = 0 := by
    omega
  rcases Int.mul_eq_zero.mp z1 with z1 | z1 <;> rcases Int.mul_eq_zero.mp z2 with z2 | z2 <;>
    exact ⟨by omega, by omega⟩

/-- Orientation-reversing similarities `z ↦ (a·z̄ + b)/d` of `ℚ² = ℚ(i)`, with
`a = p + q·i` and `b = bx + by'·i` Gaussian integers and `d > 0`. -/
structure ConjAffine where
  p : Int
  q : Int
  bx : Int
  by' : Int
  d : Int
  hd : 0 < d

/-- `(p + q i)(x - y i) + b = (p x + q y + bx) + (q x - p y + by') i`, in homogeneous form. -/
def ConjAffine.apply (g : ConjAffine) (P : Pt) : Pt :=
  ⟨g.p * P.x + g.q * P.y + g.bx * P.w, g.q * P.x - g.p * P.y + g.by' * P.w, g.d * P.w,
    Int.mul_pos g.hd P.hw⟩

theorem ConjAffine.diff_x (g : ConjAffine) (P Q : Pt) :
    (g.apply P).x * (g.apply Q).w - (g.apply Q).x * (g.apply P).w
      = g.d * (g.p * (P.x * Q.w - Q.x * P.w) + g.q * (P.y * Q.w - Q.y * P.w)) := by
  simp only [ConjAffine.apply, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem ConjAffine.diff_y (g : ConjAffine) (P Q : Pt) :
    (g.apply P).y * (g.apply Q).w - (g.apply Q).y * (g.apply P).w
      = g.d * (g.q * (P.x * Q.w - Q.x * P.w) - g.p * (P.y * Q.w - Q.y * P.w)) := by
  simp only [ConjAffine.apply, Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem norm_id (d p q X Y : Int) :
    (d * (p * X + q * Y)) * (d * (p * X + q * Y)) + (d * (q * X - p * Y)) * (d * (q * X - p * Y))
      = d * d * (p * p + q * q) * (X * X + Y * Y) := by
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm,
    Int.mul_left_comm]
  omega

theorem ConjAffine.sqNum_apply (g : ConjAffine) (P Q : Pt) :
    sqNum (g.apply P) (g.apply Q) = g.d * g.d * (g.p * g.p + g.q * g.q) * sqNum P Q := by
  unfold sqNum
  rw [g.diff_x, g.diff_y]
  exact norm_id _ _ _ _ _

theorem ConjAffine.sqDen_apply (g : ConjAffine) (P Q : Pt) :
    sqDen (g.apply P) (g.apply Q) = g.d * g.d * (g.d * g.d) * sqDen P Q := by
  simp only [sqDen, ConjAffine.apply, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- `z ↦ (a z̄ + b)/d` multiplies squared distances by `|a|²/d²`. Any `n/m` equal to this
ratio can be used. -/
theorem ConjAffine.isSimilarity (g : ConjAffine) (n m : Int) (hn : 0 < n) (hm : 0 < m)
    (h : m * (g.d * g.d * (g.p * g.p + g.q * g.q)) = n * (g.d * g.d * (g.d * g.d))) :
    IsSimilarity g.apply n m := by
  refine ⟨hn, hm, fun P Q => ?_⟩
  rw [g.sqNum_apply, g.sqDen_apply]
  generalize sqNum P Q = N
  generalize sqDen P Q = D
  generalize g.d * g.d * (g.p * g.p + g.q * g.q) = K1 at h ⊢
  generalize g.d * g.d * (g.d * g.d) = K2 at h ⊢
  have e1 : m * (K1 * N) * D = (m * K1) * (N * D) := by ac_rfl
  have e2 : n * N * (K2 * D) = (n * K2) * (N * D) := by ac_rfl
  rw [e1, e2, h]

/-! ## 3. Convex polygons and rep-tiles -/

/-- `orient A B P` is the determinant of the homogeneous coordinates of `A, B, P`. It has
the sign of `(B - A) × (P - A)`, and it is positive iff `P` is strictly left of `A → B`. -/
def orient (A B P : Pt) : Int :=
  lf (A.y * B.w - A.w * B.y) (A.w * B.x - A.x * B.w) (A.x * B.y - A.y * B.x) P

instance : Inhabited Pt := ⟨⟨0, 0, 1, by decide⟩⟩

/-- The `i`-th vertex of a vertex list. -/
def vtx (vs : List Pt) (i : Nat) : Pt := vs.getD i default

/-- `vs` lists the vertices of a convex polygon counterclockwise: it has at least 3
vertices, and every vertex other than the two endpoints of an edge lies strictly to the
left of that edge. -/
def ConvexPolygon (vs : List Pt) : Prop :=
  3 ≤ vs.length ∧
  ∀ i, i < vs.length → ∀ j, j < vs.length → j ≠ i → j ≠ (i + 1) % vs.length →
    0 < orient (vtx vs i) (vtx vs ((i + 1) % vs.length)) (vtx vs j)

instance (vs : List Pt) : Decidable (ConvexPolygon vs) := by unfold ConvexPolygon; infer_instance

/-- The closed region of the polygon: on or to the left of every edge line. -/
def InPoly (vs : List Pt) (P : Pt) : Prop :=
  ∀ i, i < vs.length → 0 ≤ orient (vtx vs i) (vtx vs ((i + 1) % vs.length)) P

/-- The interior of the polygon: strictly to the left of every edge line. -/
def InPolyInt (vs : List Pt) (P : Pt) : Prop :=
  ∀ i, i < vs.length → 0 < orient (vtx vs i) (vtx vs ((i + 1) % vs.length)) P

/-- Membership in the region respects `Pt.same`. -/
theorem InPoly.congr {vs : List Pt} {P Q : Pt} (hPQ : P.same Q) (h : InPoly vs P) :
    InPoly vs Q := fun i hi => lf_nonneg hPQ (h i hi)

/-- Membership in the interior respects `Pt.same`. -/
theorem InPolyInt.congr {vs : List Pt} {P Q : Pt} (hPQ : P.same Q) (h : InPolyInt vs P) :
    InPolyInt vs Q := fun i hi => lf_pos hPQ (h i hi)

/-- `vs` is a rep-`k` tile: there are `k` similarities `f₀, …, f_{k-1}`, each scaling
squared distances by `1/k` (so the pieces `fᵢ(tile)` are similar to the tile and pairwise
congruent), such that:
1. every piece lies in the tile;
2. the pieces cover the tile;
3. the interiors of the pieces, `fᵢ(interior)`, are pairwise disjoint. -/
def RepTile (vs : List Pt) (k : Nat) : Prop :=
  ∃ fs : List (Pt → Pt), fs.length = k ∧
    (∀ f ∈ fs, IsSimilarity f 1 k) ∧
    (∀ f ∈ fs, ∀ Q, InPoly vs Q → InPoly vs (f Q)) ∧
    (∀ P, InPoly vs P → ∃ f ∈ fs, ∃ Q, InPoly vs Q ∧ (f Q).same P) ∧
    (∀ i j, i < k → j < k → i ≠ j → ∀ Q Q', InPolyInt vs Q → InPolyInt vs Q' →
      ¬ ((fs.getD i id) Q).same ((fs.getD j id) Q'))

/-- The clause of conjecture 00000007709 under refutation: the order `k` of a convex
rep-tile is a perfect square or `k = 2`. -/
def Claim : Prop :=
  ∀ vs : List Pt, ConvexPolygon vs → ∀ k : Nat, RepTile vs k → (∃ m, k = m * m) ∨ k = 2

/-! ## 4. Triangles -/

theorem inTri_iff (A B C P : Pt) :
    InPoly [A, B, C] P ↔ 0 ≤ orient A B P ∧ 0 ≤ orient B C P ∧ 0 ≤ orient C A P := by
  constructor
  · intro h
    have h0 := h 0 (by simp)
    have h1 := h 1 (by simp)
    have h2 := h 2 (by simp)
    simp only [vtx, List.length, List.getD] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · intro ⟨h0, h1, h2⟩ i hi
    match i, hi with
    | 0, _ => simpa [vtx] using h0
    | 1, _ => simpa [vtx] using h1
    | 2, _ => simpa [vtx] using h2

theorem inTriInt_iff (A B C P : Pt) :
    InPolyInt [A, B, C] P ↔ 0 < orient A B P ∧ 0 < orient B C P ∧ 0 < orient C A P := by
  constructor
  · intro h
    have h0 := h 0 (by simp)
    have h1 := h 1 (by simp)
    have h2 := h 2 (by simp)
    simp only [vtx, List.length, List.getD] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  · intro ⟨h0, h1, h2⟩ i hi
    match i, hi with
    | 0, _ => simpa [vtx] using h0
    | 1, _ => simpa [vtx] using h1
    | 2, _ => simpa [vtx] using h2

/-! ## 5. The 1 : 2 right triangle and its five pieces -/

def ptA : Pt := ⟨0, 0, 1, by decide⟩
def ptB : Pt := ⟨10, 0, 1, by decide⟩
def ptC : Pt := ⟨0, 5, 1, by decide⟩
def ptD : Pt := ⟨2, 4, 1, by decide⟩
def ptM1 : Pt := ⟨1, 2, 1, by decide⟩
def ptM2 : Pt := ⟨6, 2, 1, by decide⟩
def ptM3 : Pt := ⟨5, 0, 1, by decide⟩

/-- The tile: right angle at `A`, legs `|AB| = 10` and `|AC| = 5`. -/
def T : List Pt := [ptA, ptB, ptC]

def piece1 : List Pt := [ptA, ptD, ptC]
def piece2 : List Pt := [ptA, ptM3, ptM1]
def piece3 : List Pt := [ptM3, ptB, ptM2]
def piece4 : List Pt := [ptM1, ptM2, ptD]
def piece5 : List Pt := [ptM3, ptM2, ptM1]

/-- `fᵢ` maps the tile onto `pieceᵢ` (`fᵢ(z) = (aᵢ z̄ + bᵢ)/5` with `|aᵢ|² = 5`). -/
def f1 : ConjAffine := ⟨-1, -2, 10, 20, 5, by decide⟩
def f2 : ConjAffine := ⟨2, -1, 5, 10, 5, by decide⟩
def f3 : ConjAffine := ⟨2, -1, 30, 10, 5, by decide⟩
def f4 : ConjAffine := ⟨2, -1, 10, 20, 5, by decide⟩
def f5 : ConjAffine := ⟨-2, 1, 25, 0, 5, by decide⟩

/-- `gᵢ` maps `pieceᵢ` back onto the tile (`gᵢ(z) = aᵢ z̄ + cᵢ`, the inverse of `fᵢ`). -/
def g1 : ConjAffine := ⟨-1, -2, 10, 0, 1, by decide⟩
def g2 : ConjAffine := ⟨2, -1, 0, 5, 1, by decide⟩
def g3 : ConjAffine := ⟨2, -1, -10, 10, 1, by decide⟩
def g4 : ConjAffine := ⟨2, -1, 0, 10, 1, by decide⟩
def g5 : ConjAffine := ⟨-2, 1, 10, -5, 1, by decide⟩

/-- The tile and all five pieces are convex polygons (nondegenerate counterclockwise
triangles). -/
theorem all_convex :
    ConvexPolygon T ∧ ConvexPolygon piece1 ∧ ConvexPolygon piece2 ∧ ConvexPolygon piece3 ∧
      ConvexPolygon piece4 ∧ ConvexPolygon piece5 := by
  decide

/-- Each `fᵢ` multiplies squared distances by exactly `1/5`. -/
theorem f_similar :
    IsSimilarity f1.apply 1 5 ∧ IsSimilarity f2.apply 1 5 ∧ IsSimilarity f3.apply 1 5 ∧
      IsSimilarity f4.apply 1 5 ∧ IsSimilarity f5.apply 1 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact ConjAffine.isSimilarity _ 1 5 (by decide) (by decide) (by decide)

/-- Sanity check: `fᵢ` sends the vertices `A, B, C` of the tile to the vertices of `pieceᵢ`. -/
theorem f_vertices :
    (f1.apply ptA).same ptD ∧ (f1.apply ptB).same ptA ∧ (f1.apply ptC).same ptC ∧
    (f2.apply ptA).same ptM1 ∧ (f2.apply ptB).same ptM3 ∧ (f2.apply ptC).same ptA ∧
    (f3.apply ptA).same ptM2 ∧ (f3.apply ptB).same ptB ∧ (f3.apply ptC).same ptM3 ∧
    (f4.apply ptA).same ptD ∧ (f4.apply ptB).same ptM2 ∧ (f4.apply ptC).same ptM1 ∧
    (f5.apply ptA).same ptM3 ∧ (f5.apply ptB).same ptM1 ∧ (f5.apply ptC).same ptM2 := by
  decide

section pieces

local macro "lin" : tactic => `(tactic|
  (simp only [T, piece1, piece2, piece3, piece4, piece5, inTri_iff, inTriInt_iff, orient, lf,
      ptA, ptB, ptC, ptD, ptM1, ptM2, ptM3, f1, f2, f3, f4, f5, g1, g2, g3, g4, g5,
      ConjAffine.apply] at *
   omega))

/-- `fᵢ(T) ⊆ pieceᵢ`. -/
theorem into (Q : Pt) (h : InPoly T Q) :
    InPoly piece1 (f1.apply Q) ∧ InPoly piece2 (f2.apply Q) ∧ InPoly piece3 (f3.apply Q) ∧
      InPoly piece4 (f4.apply Q) ∧ InPoly piece5 (f5.apply Q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> lin

/-- `fᵢ(interior T) ⊆ interior pieceᵢ`. -/
theorem into_int (Q : Pt) (h : InPolyInt T Q) :
    InPolyInt piece1 (f1.apply Q) ∧ InPolyInt piece2 (f2.apply Q) ∧
      InPolyInt piece3 (f3.apply Q) ∧ InPolyInt piece4 (f4.apply Q) ∧
      InPolyInt piece5 (f5.apply Q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> lin

/-- `pieceᵢ ⊆ fᵢ(T)`: `gᵢ` sends `pieceᵢ` into `T`, and `fᵢ ∘ gᵢ` is the identity. -/
theorem back1 (P : Pt) (h : InPoly piece1 P) : InPoly T (g1.apply P) ∧ (f1.apply (g1.apply P)).same P :=
  ⟨by lin, same_of_scale _ _ 5 (by simp only [f1, g1, ConjAffine.apply]; omega)
    (by simp only [f1, g1, ConjAffine.apply]; omega) (by simp only [f1, g1, ConjAffine.apply]; omega)⟩
theorem back2 (P : Pt) (h : InPoly piece2 P) : InPoly T (g2.apply P) ∧ (f2.apply (g2.apply P)).same P :=
  ⟨by lin, same_of_scale _ _ 5 (by simp only [f2, g2, ConjAffine.apply]; omega)
    (by simp only [f2, g2, ConjAffine.apply]; omega) (by simp only [f2, g2, ConjAffine.apply]; omega)⟩
theorem back3 (P : Pt) (h : InPoly piece3 P) : InPoly T (g3.apply P) ∧ (f3.apply (g3.apply P)).same P :=
  ⟨by lin, same_of_scale _ _ 5 (by simp only [f3, g3, ConjAffine.apply]; omega)
    (by simp only [f3, g3, ConjAffine.apply]; omega) (by simp only [f3, g3, ConjAffine.apply]; omega)⟩
theorem back4 (P : Pt) (h : InPoly piece4 P) : InPoly T (g4.apply P) ∧ (f4.apply (g4.apply P)).same P :=
  ⟨by lin, same_of_scale _ _ 5 (by simp only [f4, g4, ConjAffine.apply]; omega)
    (by simp only [f4, g4, ConjAffine.apply]; omega) (by simp only [f4, g4, ConjAffine.apply]; omega)⟩
theorem back5 (P : Pt) (h : InPoly piece5 P) : InPoly T (g5.apply P) ∧ (f5.apply (g5.apply P)).same P :=
  ⟨by lin, same_of_scale _ _ 5 (by simp only [f5, g5, ConjAffine.apply]; omega)
    (by simp only [f5, g5, ConjAffine.apply]; omega) (by simp only [f5, g5, ConjAffine.apply]; omega)⟩

/-- Every piece lies in the tile. -/
theorem pieces_sub (P : Pt) :
    (InPoly piece1 P → InPoly T P) ∧ (InPoly piece2 P → InPoly T P) ∧
      (InPoly piece3 P → InPoly T P) ∧ (InPoly piece4 P → InPoly T P) ∧
      (InPoly piece5 P → InPoly T P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> lin

/-- The pieces cover the tile. -/
theorem cover (P : Pt) (h : InPoly T P) :
    InPoly piece1 P ∨ InPoly piece2 P ∨ InPoly piece3 P ∨ InPoly piece4 P ∨ InPoly piece5 P := by
  lin

/-- The interiors of the pieces are pairwise disjoint. -/
theorem disjoint (P : Pt) :
    ¬ (InPolyInt piece1 P ∧ InPolyInt piece2 P) ∧ ¬ (InPolyInt piece1 P ∧ InPolyInt piece3 P) ∧
    ¬ (InPolyInt piece1 P ∧ InPolyInt piece4 P) ∧ ¬ (InPolyInt piece1 P ∧ InPolyInt piece5 P) ∧
    ¬ (InPolyInt piece2 P ∧ InPolyInt piece3 P) ∧ ¬ (InPolyInt piece2 P ∧ InPolyInt piece4 P) ∧
    ¬ (InPolyInt piece2 P ∧ InPolyInt piece5 P) ∧ ¬ (InPolyInt piece3 P ∧ InPolyInt piece4 P) ∧
    ¬ (InPolyInt piece3 P ∧ InPolyInt piece5 P) ∧ ¬ (InPolyInt piece4 P ∧ InPolyInt piece5 P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro ⟨h1, h2⟩ <;> lin

end pieces

/-- Non-vacuity: the tile and every piece have nonempty interior (centroids). -/
theorem interiors_nonempty :
    InPolyInt T ⟨10, 5, 3, by decide⟩ ∧ InPolyInt piece1 ⟨2, 9, 3, by decide⟩ ∧
      InPolyInt piece2 ⟨6, 2, 3, by decide⟩ ∧ InPolyInt piece3 ⟨21, 2, 3, by decide⟩ ∧
      InPolyInt piece4 ⟨9, 8, 3, by decide⟩ ∧ InPolyInt piece5 ⟨12, 4, 3, by decide⟩ := by
  simp only [T, piece1, piece2, piece3, piece4, piece5, inTriInt_iff]
  decide

/-! ## 6. The tile is a rep-5 tile -/

/-- The five piece maps, as maps of the plane. -/
def maps : List (Pt → Pt) := [f1.apply, f2.apply, f3.apply, f4.apply, f5.apply]

/-- The five pieces, as vertex lists. -/
def pieces : List (List Pt) := [piece1, piece2, piece3, piece4, piece5]

/-- `maps[i]` sends the interior of `T` into the interior of `pieces[i]`. -/
theorem maps_int (i : Nat) (hi : i < 5) (Q : Pt) (h : InPolyInt T Q) :
    InPolyInt (pieces.getD i []) ((maps.getD i id) Q) := by
  have := into_int Q h
  match i, hi with
  | 0, _ => exact this.1
  | 1, _ => exact this.2.1
  | 2, _ => exact this.2.2.1
  | 3, _ => exact this.2.2.2.1
  | 4, _ => exact this.2.2.2.2

/-- Distinct pieces have disjoint interiors. -/
theorem pieces_disjoint (i j : Nat) (hi : i < 5) (hj : j < 5) (hij : i ≠ j) (P : Pt) :
    ¬ (InPolyInt (pieces.getD i []) P ∧ InPolyInt (pieces.getD j []) P) := by
  have d := disjoint P
  match i, j, hi, hj with
  | 0, 0, _, _ | 1, 1, _, _ | 2, 2, _, _ | 3, 3, _, _ | 4, 4, _, _ => exact absurd rfl hij
  | 0, 1, _, _ => exact d.1
  | 0, 2, _, _ => exact d.2.1
  | 0, 3, _, _ => exact d.2.2.1
  | 0, 4, _, _ => exact d.2.2.2.1
  | 1, 2, _, _ => exact d.2.2.2.2.1
  | 1, 3, _, _ => exact d.2.2.2.2.2.1
  | 1, 4, _, _ => exact d.2.2.2.2.2.2.1
  | 2, 3, _, _ => exact d.2.2.2.2.2.2.2.1
  | 2, 4, _, _ => exact d.2.2.2.2.2.2.2.2.1
  | 3, 4, _, _ => exact d.2.2.2.2.2.2.2.2.2
  | 1, 0, _, _ => exact fun ⟨a, b⟩ => d.1 ⟨b, a⟩
  | 2, 0, _, _ => exact fun ⟨a, b⟩ => d.2.1 ⟨b, a⟩
  | 3, 0, _, _ => exact fun ⟨a, b⟩ => d.2.2.1 ⟨b, a⟩
  | 4, 0, _, _ => exact fun ⟨a, b⟩ => d.2.2.2.1 ⟨b, a⟩
  | 2, 1, _, _ => exact fun ⟨a, b⟩ => d.2.2.2.2.1 ⟨b, a⟩
  | 3, 1, _, _ => exact fun ⟨a, b⟩ => d.2.2.2.2.2.1 ⟨b, a⟩
  | 4, 1, _, _ => exact fun ⟨a, b⟩ => d.2.2.2.2.2.2.1 ⟨b, a⟩
  | 3, 2, _, _ => exact fun ⟨a, b⟩ => d.2.2.2.2.2.2.2.1 ⟨b, a⟩
  | 4, 2, _, _ => exact fun ⟨a, b⟩ => d.2.2.2.2.2.2.2.2.1 ⟨b, a⟩
  | 4, 3, _, _ => exact fun ⟨a, b⟩ => d.2.2.2.2.2.2.2.2.2 ⟨b, a⟩

/-- **The right triangle with legs `1 : 2` is a rep-5 tile.** -/
theorem T_rep5 : RepTile T 5 := by
  refine ⟨maps, rfl, ?_, ?_, ?_, ?_⟩
  · intro f hf
    simp only [maps, List.mem_cons, List.mem_nil_iff, or_false] at hf
    have hs := f_similar
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact hs.1
    · exact hs.2.1
    · exact hs.2.2.1
    · exact hs.2.2.2.1
    · exact hs.2.2.2.2
  · intro f hf Q hQ
    simp only [maps, List.mem_cons, List.mem_nil_iff, or_false] at hf
    have hi := into Q hQ
    have hs := pieces_sub (f Q)
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact hs.1 hi.1
    · exact hs.2.1 hi.2.1
    · exact hs.2.2.1 hi.2.2.1
    · exact hs.2.2.2.1 hi.2.2.2.1
    · exact hs.2.2.2.2 hi.2.2.2.2
  · intro P hP
    rcases cover P hP with h | h | h | h | h
    · exact ⟨f1.apply, by simp [maps], g1.apply P, back1 P h⟩
    · exact ⟨f2.apply, by simp [maps], g2.apply P, back2 P h⟩
    · exact ⟨f3.apply, by simp [maps], g3.apply P, back3 P h⟩
    · exact ⟨f4.apply, by simp [maps], g4.apply P, back4 P h⟩
    · exact ⟨f5.apply, by simp [maps], g5.apply P, back5 P h⟩
  · intro i j hi hj hij Q Q' hQ hQ' hsame
    have h1 := maps_int i hi Q hQ
    have h2 := maps_int j hj Q' hQ'
    exact pieces_disjoint i j hi hj hij _ ⟨InPolyInt.congr hsame h1, h2⟩

/-- `5` is not a perfect square. -/
theorem five_not_square : ¬ ∃ m, 5 = m * m := by
  intro ⟨m, hm⟩
  have hlt : m < 3 := by
    by_cases h : m < 3
    · exact h
    · have := Nat.mul_le_mul (show 3 ≤ m by omega) (show 3 ≤ m by omega)
      omega
  match m, hlt with
  | 0, _ => simp at hm
  | 1, _ => simp at hm
  | 2, _ => simp at hm

/-- **Main theorem.** The clause "the order `k` of a convex rep-tile must be a perfect
square or `k = 2`" is false: the convex triangle `T` is a rep-5 tile. -/
theorem conjecture_00000007709_false : ¬ Claim := by
  intro h
  rcases h T all_convex.1 5 T_rep5 with h5 | h5
  · exact five_not_square h5
  · exact absurd h5 (by decide)

end RepTile5

#print axioms RepTile5.IsSimilarity.respects
#print axioms RepTile5.ConjAffine.isSimilarity
#print axioms RepTile5.all_convex
#print axioms RepTile5.f_similar
#print axioms RepTile5.cover
#print axioms RepTile5.disjoint
#print axioms RepTile5.interiors_nonempty
#print axioms RepTile5.T_rep5
#print axioms RepTile5.conjecture_00000007709_false
