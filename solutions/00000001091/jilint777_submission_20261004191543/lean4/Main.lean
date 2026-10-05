/-!
# Conjecture 00000001091: the complete 10-arcs of `PG(2,11)` form one class

The conjecture states that the complete 10-arcs of the projective plane `PG(2,11)` form a
single isomorphism class.  Since 11 is prime, the collineation group of `PG(2,11)` is
`PΓL(3,11) = PGL(3,11)`, so isomorphism means projective equivalence: some invertible
`3 × 3` matrix over `F₁₁` maps one arc onto the other.  We prove the conjecture
(`conjecture_00000001091`).

## Model
* `F = Fin 11` (the field `F₁₁`), vectors `V`, matrices `Mat`, products `mulVec`, `mmul`.
* The 133 points are numbered `0 … 132`; `coord p` is the normalised coordinate vector
  (first nonzero coordinate `1`).  `points_cover`, `points_distinct`, `coord_ne_zero` show
  that these are exactly the 1-dimensional subspaces of `F₁₁³`.
* Lines are numbered the same way by their dual coordinates; `inc p L` is
  `coord p · coord L = 0`, and `Collinear p q r` means that `p, q, r` lie on a common line.
* `IsArc`, `IsComplete`, `IsCompleteArc k A` (a list of `k` distinct points, no three
  collinear, every other point on a secant).
* `act M p` is the image of the point `p` under the matrix `M`; `IsInv M N` says `N` is a
  two-sided inverse of `M`; `MapsOnto M A B` says `{act M a | a ∈ A} = B`;
  `ProjEquiv A B := ∃ M N, IsInv M N ∧ MapsOnto M A B`.

## Proof
1. *Algebra* (`mulVec_mmul`, `mmul_assoc`, `dot_mulVec`, …): proved for all matrices from
   the field axioms of `F₁₁` (each checked by `decide`).  Hence invertible matrices act
   bijectively on points (`act_inv`) and preserve collinearity in both directions
   (`collinear_act`, `collinear_of_act`), so they map complete `k`-arcs to complete
   `k`-arcs (`map_complete`).
2. *Frame lemma* (`frame_lemma`): for any complete 10-arc, a product of four explicit
   matrices (tables `T1data … T4data`, checked by `T1ok … T4ok`) sends its first four points
   to the frame `e₁, e₂, e₃, (1,1,1)` (points `0, 121, 132, 12`).
3. *Symmetry reduction* (`to_rep`, `reduce`): the other points of the arc lie among the 72
   points off the six sides of the frame quadrangle; these split into four orbits `O1 … O4`
   under the 24 projectivities permuting the frame (`gData`, `g1ok … g4ok`).  Taking the
   first orbit met by the arc and moving that point to the orbit representative
   (`25, 26, 27, 37`), the arc contains `frame ++ [r]` and avoids the earlier orbits.
4. *Exhaustive search* (`search`, `search_sound`, `search1 … search4`): a kernel-checked
   backtracking search over the remaining candidates (`rest1 … rest4`) shows that every
   such complete 10-arc is one of the 13 lists in `orbitData`.  Bit masks of lines through
   each point (`PL`, `ptl`) are verified against the definition of incidence (`ptl_check`).
5. *Orbit certificates* (`orbit_ok`): each of the 13 arcs is mapped onto the representative
   `R` by an explicit invertible matrix.
6. `complete10_equiv` combines these; `R_complete` shows that a complete 10-arc exists,
   and `C10_not_complete` exhibits a 10-arc (ten points of a conic) that is not complete.

All finite checks use `decide` or `decide +kernel` (kernel evaluation only; no compiled code is trusted).
-/

namespace PG211

/-- The field with 11 elements. -/
abbrev F := Fin 11

/-! ## Field facts and linear algebra over `F₁₁` -/

theorem f_add_comm (a b : F) : a + b = b + a := by revert a b; decide
theorem f_add_assoc (a b c : F) : a + b + c = a + (b + c) := by revert a b c; decide
theorem f_add_left_comm (a b c : F) : a + (b + c) = b + (a + c) := by revert a b c; decide
theorem f_mul_comm (a b : F) : a * b = b * a := by revert a b; decide
theorem f_mul_assoc (a b c : F) : a * b * c = a * (b * c) := by revert a b c; decide
theorem f_mul_left_comm (a b c : F) : a * (b * c) = b * (a * c) := by revert a b c; decide
theorem f_mul_add (a b c : F) : a * (b + c) = a * b + a * c := by revert a b c; decide
theorem f_add_mul (a b c : F) : (a + b) * c = a * c + b * c := by revert a b c; decide
theorem f_mul_one (a : F) : a * 1 = a := by revert a; decide
theorem f_one_mul (a : F) : 1 * a = a := by revert a; decide
theorem f_mul_zero (a : F) : a * 0 = 0 := by revert a; decide
theorem f_zero_mul (a : F) : 0 * a = 0 := by revert a; decide
theorem f_add_zero (a : F) : a + 0 = a := by revert a; decide
theorem f_zero_add (a : F) : 0 + a = a := by revert a; decide
theorem f_mul_eq_zero (a b : F) : a * b = 0 → a = 0 ∨ b = 0 := by revert a b; decide

/-- Vectors of `F₁₁³`. -/
structure V where
  x : F
  y : F
  z : F
deriving DecidableEq

/-- `3 × 3` matrices over `F₁₁`, row by row: `(a b c / d e f / g h i)`. -/
structure Mat where
  a : F
  b : F
  c : F
  d : F
  e : F
  f : F
  g : F
  h : F
  i : F
deriving DecidableEq

def V.zero : V := ⟨0, 0, 0⟩

def mulVec (M : Mat) (v : V) : V :=
  ⟨M.a * v.x + M.b * v.y + M.c * v.z, M.d * v.x + M.e * v.y + M.f * v.z,
   M.g * v.x + M.h * v.y + M.i * v.z⟩

def mmul (M N : Mat) : Mat :=
  ⟨M.a*N.a + M.b*N.d + M.c*N.g, M.a*N.b + M.b*N.e + M.c*N.h, M.a*N.c + M.b*N.f + M.c*N.i,
   M.d*N.a + M.e*N.d + M.f*N.g, M.d*N.b + M.e*N.e + M.f*N.h, M.d*N.c + M.e*N.f + M.f*N.i,
   M.g*N.a + M.h*N.d + M.i*N.g, M.g*N.b + M.h*N.e + M.i*N.h, M.g*N.c + M.h*N.f + M.i*N.i⟩

def one : Mat := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

def tr (M : Mat) : Mat := ⟨M.a, M.d, M.g, M.b, M.e, M.h, M.c, M.f, M.i⟩

def smul (c : F) (v : V) : V := ⟨c * v.x, c * v.y, c * v.z⟩

def dot (u v : V) : F := u.x * v.x + u.y * v.y + u.z * v.z

/-- `N` is a two-sided inverse of `M`. -/
def IsInv (M N : Mat) : Prop := mmul M N = one ∧ mmul N M = one

theorem mulVec_mmul (M N : Mat) (v : V) : mulVec (mmul M N) v = mulVec M (mulVec N v) := by
  cases M; cases N; cases v
  simp only [mulVec, mmul, V.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [f_mul_add, f_add_mul, f_mul_assoc, f_add_assoc] <;>
  simp only [f_mul_comm, f_mul_left_comm, f_add_comm, f_add_left_comm]

theorem mmul_assoc (M N P : Mat) : mmul (mmul M N) P = mmul M (mmul N P) := by
  cases M; cases N; cases P
  simp only [mmul, Mat.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [f_mul_add, f_add_mul, f_mul_assoc, f_add_assoc] <;>
  simp only [f_mul_comm, f_mul_left_comm, f_add_comm, f_add_left_comm]

theorem mmul_one (M : Mat) : mmul M one = M := by
  cases M
  simp only [mmul, one, f_mul_one, f_mul_zero, f_add_zero, f_zero_add]

theorem one_mmul (M : Mat) : mmul one M = M := by
  cases M
  simp only [mmul, one, f_one_mul, f_zero_mul, f_add_zero, f_zero_add]

theorem mulVec_one (v : V) : mulVec one v = v := by
  cases v
  simp only [mulVec, one, f_one_mul, f_zero_mul, f_add_zero, f_zero_add]

theorem mulVec_zero (M : Mat) : mulVec M V.zero = V.zero := by
  cases M
  simp only [mulVec, V.zero, f_mul_zero, f_add_zero]

theorem mulVec_smul (M : Mat) (c : F) (v : V) : mulVec M (smul c v) = smul c (mulVec M v) := by
  cases M; cases v
  simp only [mulVec, smul, V.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [f_mul_add, f_add_mul, f_mul_assoc, f_add_assoc] <;>
  simp only [f_mul_comm, f_mul_left_comm, f_add_comm, f_add_left_comm]

theorem dot_smul (c d : F) (u v : V) : dot (smul c u) (smul d v) = c * (d * dot u v) := by
  cases u; cases v
  simp only [dot, smul]
  simp only [f_mul_add, f_add_mul, f_mul_assoc, f_add_assoc]
  simp only [f_mul_comm, f_mul_left_comm, f_add_comm, f_add_left_comm]

theorem dot_mulVec (N : Mat) (u w : V) : dot (mulVec N u) w = dot u (mulVec (tr N) w) := by
  cases N; cases u; cases w
  simp only [dot, mulVec, tr]
  simp only [f_mul_add, f_add_mul, f_mul_assoc, f_add_assoc]
  simp only [f_mul_comm, f_mul_left_comm, f_add_comm, f_add_left_comm]

theorem tr_mmul (M N : Mat) : tr (mmul M N) = mmul (tr N) (tr M) := by
  cases M; cases N
  simp only [tr, mmul, Mat.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [f_mul_comm, f_mul_left_comm, f_add_comm, f_add_left_comm]

theorem tr_one : tr one = one := rfl

theorem isInv_symm {M N : Mat} (h : IsInv M N) : IsInv N M := ⟨h.2, h.1⟩

theorem isInv_comp {M N M' N' : Mat} (h : IsInv M N) (h' : IsInv M' N') :
    IsInv (mmul M' M) (mmul N N') := by
  constructor
  · rw [mmul_assoc, ← mmul_assoc M N N', h.1, one_mmul, h'.1]
  · rw [mmul_assoc, ← mmul_assoc N' M' M, h'.2, one_mmul, h.2]


/-! ## The 133 points of `PG(2,11)` -/

/-- Inverse in `F₁₁` (with `inv11 0 = 0`). -/
def inv11 (a : F) : F :=
  match a.val with
  | 1 => 1 | 2 => 6 | 3 => 4 | 4 => 3 | 5 => 9 | 6 => 2 | 7 => 8 | 8 => 7 | 9 => 5 | 10 => 10
  | _ => 0

theorem inv11_mul : ∀ a : F, a ≠ 0 → inv11 a * a = 1 := by decide
theorem inv11_ne : ∀ a : F, a ≠ 0 → inv11 a ≠ 0 := by decide
theorem f_mul_ne : ∀ c a : F, c ≠ 0 → a ≠ 0 → c * a ≠ 0 := by decide
theorem inv11_smul : ∀ c a b : F, c ≠ 0 → a ≠ 0 → inv11 (c * a) * (c * b) = inv11 a * b := by
  decide +kernel

/-- The scalar normalising `v`: the inverse of its first nonzero coordinate. -/
def nscale (v : V) : F :=
  if v.x ≠ 0 then inv11 v.x else if v.y ≠ 0 then inv11 v.y else if v.z ≠ 0 then inv11 v.z else 1

/-- Normal form of a vector: scaled so that its first nonzero coordinate is `1`. -/
def norm (v : V) : V := smul (nscale v) v

def fin11 (n : Nat) : F := ⟨n % 11, Nat.mod_lt _ (by decide)⟩

/-- Coordinates (as natural numbers `< 11`) of the point number `p`:
`p = 11a + b < 121` is `(1,a,b)`, `121 + b` is `(0,1,b)` and `132` is `(0,0,1)`. -/
def cx (p : Nat) : Nat := if p < 121 then 1 else 0
def cy (p : Nat) : Nat := if p < 121 then p / 11 else if p < 132 then 1 else 0
def cz (p : Nat) : Nat := if p < 121 then p % 11 else if p < 132 then p - 121 else 1

/-- The normalised coordinate vector of the point number `p < 133`. -/
def coord (p : Nat) : V := ⟨fin11 (cx p), fin11 (cy p), fin11 (cz p)⟩

/-- Number of a normalised vector (inverse of `coord`). -/
def idx (v : V) : Nat :=
  if v.x = 1 then 11 * v.y.val + v.z.val
  else if v.x = 0 ∧ v.y = 1 then 121 + v.z.val else 132

/-- Action of the matrix `M` on the point number `p`: `p ↦ [M · coord p]`. -/
def act (M : Mat) (p : Nat) : Nat := idx (norm (mulVec M (coord p)))

/-- Incidence: point `p` lies on line `L`.  Lines are numbered like points, by their
normalised dual coordinates, and `p` lies on `L` iff `coord p · coord L = 0`. -/
def inc (p L : Nat) : Prop := dot (coord p) (coord L) = 0

instance (p L : Nat) : Decidable (inc p L) := by unfold inc; infer_instance

/-- Three points are collinear if they lie on a common line. -/
def Collinear (p q r : Nat) : Prop := ∃ L, L < 133 ∧ inc p L ∧ inc q L ∧ inc r L

theorem forall_V {P : V → Prop} (h : ∀ x y z : F, P ⟨x, y, z⟩) (v : V) : P v := by
  cases v; exact h _ _ _

theorem nscale_ne (v : V) : nscale v ≠ 0 := by
  rcases v with ⟨x, y, z⟩
  unfold nscale
  by_cases hx : x = 0
  · rw [if_neg (fun h => h hx)]
    by_cases hy : y = 0
    · rw [if_neg (fun h => h hy)]
      by_cases hz : z = 0
      · rw [if_neg (fun h => h hz)]; decide
      · rw [if_pos hz]; exact inv11_ne z hz
    · rw [if_pos hy]; exact inv11_ne y hy
  · rw [if_pos hx]; exact inv11_ne x hx

theorem norm_form (v : V) (hv : v ≠ V.zero) :
    (∃ a b : F, norm v = ⟨1, a, b⟩) ∨ (∃ b : F, norm v = ⟨0, 1, b⟩) ∨ norm v = ⟨0, 0, 1⟩ := by
  rcases v with ⟨x, y, z⟩
  unfold norm nscale smul
  by_cases hx : x = 0
  · rw [if_neg (fun h => h hx)]
    subst hx
    by_cases hy : y = 0
    · rw [if_neg (fun h => h hy)]
      subst hy
      by_cases hz : z = 0
      · exact absurd (by rw [hz]; rfl) hv
      · rw [if_pos hz]
        refine Or.inr (Or.inr ?_)
        simp only [inv11_mul z hz, f_mul_zero]
    · rw [if_pos hy]
      refine Or.inr (Or.inl ⟨inv11 y * z, ?_⟩)
      simp only [inv11_mul y hy, f_mul_zero]
  · rw [if_pos hx]
    exact Or.inl ⟨inv11 x * y, inv11 x * z, by simp only [inv11_mul x hx]⟩

theorem coord_idx_1 : ∀ a b : F, coord (idx ⟨1, a, b⟩) = ⟨1, a, b⟩ := by decide +kernel
theorem coord_idx_2 : ∀ b : F, coord (idx ⟨0, 1, b⟩) = ⟨0, 1, b⟩ := by decide +kernel
theorem coord_idx_3 : coord (idx ⟨0, 0, 1⟩) = ⟨0, 0, 1⟩ := by decide

theorem coord_idx_norm (v : V) (h : v ≠ V.zero) : coord (idx (norm v)) = norm v := by
  rcases norm_form v h with ⟨a, b, e⟩ | ⟨b, e⟩ | e <;> rw [e]
  · exact coord_idx_1 a b
  · exact coord_idx_2 b
  · exact coord_idx_3

theorem f_mul_ne_iff (c a : F) (hc : c ≠ 0) : (c * a ≠ 0) ↔ (a ≠ 0) :=
  ⟨fun h ha => h (by rw [ha, f_mul_zero]), f_mul_ne c a hc⟩

theorem norm_smul (c : F) (hc : c ≠ 0) (v : V) : norm (smul c v) = norm v := by
  rcases v with ⟨x, y, z⟩
  unfold norm nscale smul
  simp only [f_mul_ne_iff c _ hc]
  by_cases hx : x = 0
  · subst hx
    by_cases hy : y = 0
    · subst hy
      by_cases hz : z = 0
      · subst hz; simp [f_mul_zero]
      · simp [hz, inv11_smul c z _ hc hz, f_mul_zero]
    · simp [hy, inv11_smul c y _ hc hy, f_mul_zero]
  · simp [hx, inv11_smul c x _ hc hx]

theorem idx_lt (v : V) : idx v < 133 := by
  unfold idx
  have := v.y.isLt; have := v.z.isLt
  split
  · omega
  · split <;> omega

theorem coord_ok : ∀ p, p < 133 → coord p ≠ V.zero ∧ idx (norm (coord p)) = p := by
  decide +kernel

/-! ## Projectivities act on points and preserve collinearity -/

theorem act_lt (M : Mat) (p : Nat) : act M p < 133 := idx_lt _

theorem mulVec_ne_zero {M N : Mat} (h : mmul N M = one) {v : V} (hv : v ≠ V.zero) :
    mulVec M v ≠ V.zero := by
  intro h0
  have := congrArg (mulVec N) h0
  rw [← mulVec_mmul, h, mulVec_one, mulVec_zero] at this
  exact hv this

theorem coord_act {M N : Mat} (h : mmul N M = one) {p : Nat} (hp : p < 133) :
    ∃ c : F, c ≠ 0 ∧ coord (act M p) = smul c (mulVec M (coord p)) :=
  ⟨_, nscale_ne _, coord_idx_norm _ (mulVec_ne_zero h (coord_ok p hp).1)⟩

theorem act_comp {M1 N1 : Mat} (M2 : Mat) (h : mmul N1 M1 = one) {p : Nat} (hp : p < 133) :
    act M2 (act M1 p) = act (mmul M2 M1) p := by
  obtain ⟨c, hc, hcp⟩ := coord_act h hp
  show idx (norm (mulVec M2 (coord (act M1 p)))) = idx (norm (mulVec (mmul M2 M1) (coord p)))
  rw [hcp, mulVec_smul, norm_smul c hc, mulVec_mmul]

theorem act_one {p : Nat} (hp : p < 133) : act one p = p := by
  show idx (norm (mulVec one (coord p))) = p
  rw [mulVec_one]; exact (coord_ok p hp).2

theorem act_inv {M N : Mat} (h : IsInv M N) {p : Nat} (hp : p < 133) : act N (act M p) = p := by
  rw [act_comp N h.2 hp, h.2, act_one hp]

theorem act_inj {M N : Mat} (h : IsInv M N) {p q : Nat} (hp : p < 133) (hq : q < 133)
    (he : act M p = act M q) : p = q := by
  rw [← act_inv h hp, ← act_inv h hq, he]

/-- Action on lines (by the inverse transpose). -/
def lact (N : Mat) (L : Nat) : Nat := idx (norm (mulVec (tr N) (coord L)))

theorem inc_act {M N : Mat} (h : IsInv M N) {p L : Nat} (hp : p < 133) (hL : L < 133)
    (hi : inc p L) : inc (act M p) (lact N L) := by
  obtain ⟨c, _, hcp⟩ := coord_act h.2 hp
  have hw : mulVec (tr N) (coord L) ≠ V.zero := by
    apply mulVec_ne_zero (N := tr M) _ (coord_ok L hL).1
    rw [← tr_mmul, h.2, tr_one]
  have hcL := coord_idx_norm _ hw
  unfold inc at hi ⊢
  show dot (coord (act M p)) (coord (idx (norm (mulVec (tr N) (coord L))))) = 0
  rw [hcp, hcL]
  show dot (smul c _) (smul (nscale _) _) = 0
  rw [dot_smul, ← dot_mulVec, ← mulVec_mmul, h.2, mulVec_one, hi, f_mul_zero, f_mul_zero]

theorem collinear_act {M N : Mat} (h : IsInv M N) {p q r : Nat} (hp : p < 133) (hq : q < 133)
    (hr : r < 133) (hc : Collinear p q r) : Collinear (act M p) (act M q) (act M r) := by
  obtain ⟨L, hL, h1, h2, h3⟩ := hc
  exact ⟨lact N L, idx_lt _, inc_act h hp hL h1, inc_act h hq hL h2, inc_act h hr hL h3⟩

theorem collinear_of_act {M N : Mat} (h : IsInv M N) {p q r : Nat} (hp : p < 133)
    (hq : q < 133) (hr : r < 133) (hc : Collinear (act M p) (act M q) (act M r)) :
    Collinear p q r := by
  have := collinear_act (isInv_symm h) (act_lt M p) (act_lt M q) (act_lt M r) hc
  rwa [act_inv h hp, act_inv h hq, act_inv h hr] at this

/-! ## Arcs, complete arcs and projective equivalence -/

/-- An arc: a list of points (numbers `< 133`) no three distinct of which are collinear. -/
def IsArc (A : List Nat) : Prop :=
  (∀ p ∈ A, p < 133) ∧
    ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, p ≠ q → p ≠ r → q ≠ r → ¬ Collinear p q r

/-- Completeness: every point off the arc lies on a secant (a line through two points of
the arc), i.e. the arc cannot be extended to a larger arc. -/
def IsComplete (A : List Nat) : Prop :=
  ∀ p, p < 133 → p ∉ A → ∃ q ∈ A, ∃ r ∈ A, q ≠ r ∧ Collinear q r p

/-- A complete `k`-arc: `k` distinct points forming a complete arc. -/
def IsCompleteArc (k : Nat) (A : List Nat) : Prop :=
  A.Nodup ∧ A.length = k ∧ IsArc A ∧ IsComplete A

/-- The point set `B` is the image of the point set `A` under the matrix `M`. -/
def MapsOnto (M : Mat) (A B : List Nat) : Prop := ∀ x, x ∈ B ↔ ∃ a ∈ A, act M a = x

/-- Projective equivalence: some invertible matrix maps `A` onto `B`. -/
def ProjEquiv (A B : List Nat) : Prop := ∃ M N : Mat, IsInv M N ∧ MapsOnto M A B

/-! ## Fast incidence tables (checked against the definition) -/

/-- Incidence in natural-number arithmetic. -/
def incB (p L : Nat) : Bool := (cx p * cx L + cy p * cy L + cz p * cz L) % 11 == 0

theorem cx_lt (p : Nat) : cx p < 11 := by unfold cx; split <;> omega
theorem cy_lt (p : Nat) : cy p < 11 := by unfold cy; split <;> (try split) <;> omega
theorem cz_lt (p : Nat) : cz p < 11 := by unfold cz; split <;> (try split) <;> omega

theorem dot_val (u v : V) :
    (dot u v).val = (u.x.val * v.x.val + u.y.val * v.y.val + u.z.val * v.z.val) % 11 := by
  simp only [dot, Fin.val_add, Fin.val_mul]
  generalize u.x.val * v.x.val = a
  generalize u.y.val * v.y.val = b
  generalize u.z.val * v.z.val = c
  omega

theorem inc_iff (p L : Nat) : inc p L ↔ incB p L = true := by
  unfold inc incB
  rw [beq_iff_eq, Fin.ext_iff, dot_val]
  simp only [coord, fin11, Nat.mod_eq_of_lt (cx_lt _), Nat.mod_eq_of_lt (cy_lt _),
    Nat.mod_eq_of_lt (cz_lt _)]
  exact Iff.rfl

/-! ## Data: line masks, transversal matrices, orbits, search lists and orbit certificates -/

/-- Table of the lines through each point: bits `133x .. 133x+132` of `PL` are the lines through point `x`. -/
def PL : Nat := 0x200400801002004008010020040080100280080080080080080080080080080082002080004100008200010400020800040404000880010002200040008800100020104001000480020008002400100040012000080402010080000804020100800008022001000800400280040020010008004400040404000080808080001010100002100040800020408000204080002040001020080008400042000210001080008000a000020080200802008020080200800006000000000000000000000000000000ffe8000100401004010040100401000008020200042000210001080008400040004200401000040810000408100004080002040400202000040404040000808080001010008200100080050008004002001000a0020002010080400004020100804000040200402000900040010004800200080024000400440008001100020004400080011000810000820001040002080004100008200024004004004004004004004004006004000000000000000000000000000ffe000800040201008000080402010080400004800200802008000040100401004010040008004800200080024001000480020008010200021000100010800084000420002004010002200040008800110002000440010010200008100004081000040810000404000820001040002082000104000208008040000808080001010101000020202000080800800800800c004004004004004000840020010008005000800400200140080000000000000ffe000000000000000008001010100002020200004040404000080400220004000880010002200044000808000802008020080200001004010040100040050008004002001000a001000800402000820001040002080004104000208000808000840004200020002100010800084010000100804020100001008040201000020800800800800800800c0040040040040200008102000081000040810000408002040010004800200080024001000480100000000000000000007ff000000000000800408000204080002040001020400011001008000080402010080000804020100101000082000104000208000410400020800040100401004010040000200802008100004040404000080808000101010100004400100040012000800200090004001000840040040040040040040060020020004001080008400042000200021000108000401000a00100080040020014002001000804000880010002200040008800110020000000000000000000001ffc000000000801000082080004100008200010400020080100048002000900040010004800200020040028004002001000a001000800402004000102040001020400010204000108010000080200802008020080200802000020040060020020020020020020020020080100022000440008001100020004400801000010080402010080000804020100200400008080808000101010100002020020040004200021000108000840004200400000ffe00000000000000000000000000804000420002100010800080008400042008000101010100002020200004040402000804020000201008040200002010080084000800110002000440008001100020008800800800800800800800800c0040080002008020080200802008000040100408000408100004081000040800020408000202001000a00100080040020014002000200240010004001200080020009000400800410000820001040002080004104008000000000000000000000000ffe000000081000200044000880010002200040008010080040028004002001000a0010008004100010001080008400042000210001000200800800c00400400400400400400400404001000480020009000400100048004001010000202020200004040404000088008020000100401004010040100401000400041000082080004100008200010401000804000040201008040200002010080200040800020408000204080002040801000000007ff000000000000000000000000840010004001200080024001000400104040001020000810200008102000081000080400400400600200200200200200204000804020000201008040201000010080200210001000108000840004200021000200800041000082080004100008200010010200100080050008004002001400200800401004000020080200802008020080010004400080011000220004000880010080004040400008080808000101010100200000000001ffc00000000000000000000090008004002001000a00100080040020020400400400400400600200200200200800808000101010000202020200004040100800041000082000104100008200010100010204000102000081020000810200010400080011000200044000880010002010008400042000200021000108000840002008002400100040012000800240010080010040100401000008020080200802020000402010080400004020100804020040000000000000000ffe0000000000000000800c00400400400400400400400400408000410400020800041000082000104001000220004400080011000200044000800400120008002400100040012000800208000080402010080400004020100804000080050008004002001400200100080041000020202020000404040400008080800400010204000102040001020400010200080008400042000210001080008400040800004010040100401004010040100400800ffe0000000000000000000000000000008020040080100200400801002004008004200400801002004008010020040080002040080100200400801002004008010001010020040080100200400801002004000a0040080100200400801002004008000040200400801002004008010020040080024008010020040080100200400801000011002004008010020040080100200400008200400801002004008010020040080006004008010020040080100200400801ffe000000000000000000000000000000

def T1data : List (Mat × Mat) := [
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 10, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 9, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 2, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 8, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 3, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 7, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 4, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 6, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 5, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 5, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 6, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 4, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 7, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 3, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 8, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 2, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 9, 1, 0, 10, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 10, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 1, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 9, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 2, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 8, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 3, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 7, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 4, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 6, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 5, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 5, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 6, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 4, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 7, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 3, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 8, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 2, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 9, 0, 1⟩),
  (⟨1, 0, 0, 1, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 10, 1, 0, 10, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 0, 1, 0, 0, 0, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 10, 1⟩, ⟨0, 1, 0, 1, 0, 0, 1, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 9, 1⟩, ⟨0, 1, 0, 1, 0, 0, 2, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 8, 1⟩, ⟨0, 1, 0, 1, 0, 0, 3, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 7, 1⟩, ⟨0, 1, 0, 1, 0, 0, 4, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 6, 1⟩, ⟨0, 1, 0, 1, 0, 0, 5, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 5, 1⟩, ⟨0, 1, 0, 1, 0, 0, 6, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 4, 1⟩, ⟨0, 1, 0, 1, 0, 0, 7, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 3, 1⟩, ⟨0, 1, 0, 1, 0, 0, 8, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 2, 1⟩, ⟨0, 1, 0, 1, 0, 0, 9, 0, 1⟩),
  (⟨0, 1, 0, 1, 0, 0, 0, 1, 1⟩, ⟨0, 1, 0, 1, 0, 0, 10, 0, 1⟩),
  (⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩)]

def T2data : List (Mat × Mat) := [
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 0, 10, 0⟩),
  (⟨1, 10, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 10⟩, ⟨1, 1, 0, 0, 1, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 5⟩, ⟨1, 1, 0, 0, 1, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 7⟩, ⟨1, 1, 0, 0, 1, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 8⟩, ⟨1, 1, 0, 0, 1, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 2⟩, ⟨1, 1, 0, 0, 1, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 9⟩, ⟨1, 1, 0, 0, 1, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 3⟩, ⟨1, 1, 0, 0, 1, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 4⟩, ⟨1, 1, 0, 0, 1, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 6⟩, ⟨1, 1, 0, 0, 1, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 1⟩, ⟨1, 1, 0, 0, 1, 1, 0, 10, 0⟩),
  (⟨1, 5, 0, 0, 6, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 2, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 9⟩, ⟨1, 1, 0, 0, 2, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 10⟩, ⟨1, 1, 0, 0, 2, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 3⟩, ⟨1, 1, 0, 0, 2, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 5⟩, ⟨1, 1, 0, 0, 2, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 4⟩, ⟨1, 1, 0, 0, 2, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 7⟩, ⟨1, 1, 0, 0, 2, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 6⟩, ⟨1, 1, 0, 0, 2, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 8⟩, ⟨1, 1, 0, 0, 2, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 1⟩, ⟨1, 1, 0, 0, 2, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 2⟩, ⟨1, 1, 0, 0, 2, 1, 0, 10, 0⟩),
  (⟨1, 7, 0, 0, 4, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 3, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 8⟩, ⟨1, 1, 0, 0, 3, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 4⟩, ⟨1, 1, 0, 0, 3, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 10⟩, ⟨1, 1, 0, 0, 3, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 2⟩, ⟨1, 1, 0, 0, 3, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 6⟩, ⟨1, 1, 0, 0, 3, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 5⟩, ⟨1, 1, 0, 0, 3, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 9⟩, ⟨1, 1, 0, 0, 3, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 1⟩, ⟨1, 1, 0, 0, 3, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 7⟩, ⟨1, 1, 0, 0, 3, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 3⟩, ⟨1, 1, 0, 0, 3, 1, 0, 10, 0⟩),
  (⟨1, 8, 0, 0, 3, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 4, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 7⟩, ⟨1, 1, 0, 0, 4, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 9⟩, ⟨1, 1, 0, 0, 4, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 6⟩, ⟨1, 1, 0, 0, 4, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 10⟩, ⟨1, 1, 0, 0, 4, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 8⟩, ⟨1, 1, 0, 0, 4, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 3⟩, ⟨1, 1, 0, 0, 4, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 1⟩, ⟨1, 1, 0, 0, 4, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 5⟩, ⟨1, 1, 0, 0, 4, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 2⟩, ⟨1, 1, 0, 0, 4, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 4⟩, ⟨1, 1, 0, 0, 4, 1, 0, 10, 0⟩),
  (⟨1, 2, 0, 0, 9, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 5, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 6⟩, ⟨1, 1, 0, 0, 5, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 3⟩, ⟨1, 1, 0, 0, 5, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 2⟩, ⟨1, 1, 0, 0, 5, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 7⟩, ⟨1, 1, 0, 0, 5, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 10⟩, ⟨1, 1, 0, 0, 5, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 1⟩, ⟨1, 1, 0, 0, 5, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 4⟩, ⟨1, 1, 0, 0, 5, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 9⟩, ⟨1, 1, 0, 0, 5, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 8⟩, ⟨1, 1, 0, 0, 5, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 5⟩, ⟨1, 1, 0, 0, 5, 1, 0, 10, 0⟩),
  (⟨1, 9, 0, 0, 2, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 6, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 5⟩, ⟨1, 1, 0, 0, 6, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 8⟩, ⟨1, 1, 0, 0, 6, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 9⟩, ⟨1, 1, 0, 0, 6, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 4⟩, ⟨1, 1, 0, 0, 6, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 1⟩, ⟨1, 1, 0, 0, 6, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 10⟩, ⟨1, 1, 0, 0, 6, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 7⟩, ⟨1, 1, 0, 0, 6, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 2⟩, ⟨1, 1, 0, 0, 6, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 3⟩, ⟨1, 1, 0, 0, 6, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 6⟩, ⟨1, 1, 0, 0, 6, 1, 0, 10, 0⟩),
  (⟨1, 3, 0, 0, 8, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 7, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 4⟩, ⟨1, 1, 0, 0, 7, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 2⟩, ⟨1, 1, 0, 0, 7, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 5⟩, ⟨1, 1, 0, 0, 7, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 1⟩, ⟨1, 1, 0, 0, 7, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 3⟩, ⟨1, 1, 0, 0, 7, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 8⟩, ⟨1, 1, 0, 0, 7, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 10⟩, ⟨1, 1, 0, 0, 7, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 6⟩, ⟨1, 1, 0, 0, 7, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 9⟩, ⟨1, 1, 0, 0, 7, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 7⟩, ⟨1, 1, 0, 0, 7, 1, 0, 10, 0⟩),
  (⟨1, 4, 0, 0, 7, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 8, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 3⟩, ⟨1, 1, 0, 0, 8, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 7⟩, ⟨1, 1, 0, 0, 8, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 1⟩, ⟨1, 1, 0, 0, 8, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 9⟩, ⟨1, 1, 0, 0, 8, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 5⟩, ⟨1, 1, 0, 0, 8, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 6⟩, ⟨1, 1, 0, 0, 8, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 2⟩, ⟨1, 1, 0, 0, 8, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 10⟩, ⟨1, 1, 0, 0, 8, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 4⟩, ⟨1, 1, 0, 0, 8, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 8⟩, ⟨1, 1, 0, 0, 8, 1, 0, 10, 0⟩),
  (⟨1, 6, 0, 0, 5, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 9, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 2⟩, ⟨1, 1, 0, 0, 9, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 1⟩, ⟨1, 1, 0, 0, 9, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 8⟩, ⟨1, 1, 0, 0, 9, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 6⟩, ⟨1, 1, 0, 0, 9, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 7⟩, ⟨1, 1, 0, 0, 9, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 4⟩, ⟨1, 1, 0, 0, 9, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 5⟩, ⟨1, 1, 0, 0, 9, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 3⟩, ⟨1, 1, 0, 0, 9, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 10⟩, ⟨1, 1, 0, 0, 9, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 9⟩, ⟨1, 1, 0, 0, 9, 1, 0, 10, 0⟩),
  (⟨1, 1, 0, 0, 10, 0, 0, 0, 1⟩, ⟨1, 1, 0, 0, 10, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 0, 1, 0, 1, 1⟩, ⟨1, 1, 0, 0, 10, 1, 0, 1, 0⟩),
  (⟨1, 0, 5, 0, 0, 6, 0, 1, 6⟩, ⟨1, 1, 0, 0, 10, 1, 0, 2, 0⟩),
  (⟨1, 0, 7, 0, 0, 4, 0, 1, 4⟩, ⟨1, 1, 0, 0, 10, 1, 0, 3, 0⟩),
  (⟨1, 0, 8, 0, 0, 3, 0, 1, 3⟩, ⟨1, 1, 0, 0, 10, 1, 0, 4, 0⟩),
  (⟨1, 0, 2, 0, 0, 9, 0, 1, 9⟩, ⟨1, 1, 0, 0, 10, 1, 0, 5, 0⟩),
  (⟨1, 0, 9, 0, 0, 2, 0, 1, 2⟩, ⟨1, 1, 0, 0, 10, 1, 0, 6, 0⟩),
  (⟨1, 0, 3, 0, 0, 8, 0, 1, 8⟩, ⟨1, 1, 0, 0, 10, 1, 0, 7, 0⟩),
  (⟨1, 0, 4, 0, 0, 7, 0, 1, 7⟩, ⟨1, 1, 0, 0, 10, 1, 0, 8, 0⟩),
  (⟨1, 0, 6, 0, 0, 5, 0, 1, 5⟩, ⟨1, 1, 0, 0, 10, 1, 0, 9, 0⟩),
  (⟨1, 0, 1, 0, 0, 10, 0, 1, 10⟩, ⟨1, 1, 0, 0, 10, 1, 0, 10, 0⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 0, 1, 0, 1, 10⟩, ⟨1, 0, 0, 0, 1, 1, 0, 1, 0⟩),
  (⟨1, 0, 0, 0, 0, 6, 0, 1, 5⟩, ⟨1, 0, 0, 0, 1, 1, 0, 2, 0⟩),
  (⟨1, 0, 0, 0, 0, 4, 0, 1, 7⟩, ⟨1, 0, 0, 0, 1, 1, 0, 3, 0⟩),
  (⟨1, 0, 0, 0, 0, 3, 0, 1, 8⟩, ⟨1, 0, 0, 0, 1, 1, 0, 4, 0⟩),
  (⟨1, 0, 0, 0, 0, 9, 0, 1, 2⟩, ⟨1, 0, 0, 0, 1, 1, 0, 5, 0⟩),
  (⟨1, 0, 0, 0, 0, 2, 0, 1, 9⟩, ⟨1, 0, 0, 0, 1, 1, 0, 6, 0⟩),
  (⟨1, 0, 0, 0, 0, 8, 0, 1, 3⟩, ⟨1, 0, 0, 0, 1, 1, 0, 7, 0⟩),
  (⟨1, 0, 0, 0, 0, 7, 0, 1, 4⟩, ⟨1, 0, 0, 0, 1, 1, 0, 8, 0⟩),
  (⟨1, 0, 0, 0, 0, 5, 0, 1, 6⟩, ⟨1, 0, 0, 0, 1, 1, 0, 9, 0⟩),
  (⟨1, 0, 0, 0, 0, 10, 0, 1, 1⟩, ⟨1, 0, 0, 0, 1, 1, 0, 10, 0⟩),
  (⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩)]

def T3data : List (Mat × Mat) := [
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 0, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 0, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 0, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 0, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 0, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 0, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 0, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 0, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 0, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 10, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 5, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 7, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 8, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 2, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 9, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 3, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 4, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 6, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 1, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 1, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 9, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 10, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 3, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 5, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 4, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 7, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 6, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 8, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 1, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 2, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 2, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 8, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 4, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 10, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 2, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 6, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 5, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 9, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 1, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 7, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 3, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 3, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 7, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 9, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 6, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 10, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 8, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 3, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 1, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 5, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 2, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 4, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 4, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 6, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 3, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 2, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 7, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 10, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 1, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 4, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 9, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 8, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 5, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 5, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 5, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 8, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 9, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 4, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 1, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 10, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 7, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 2, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 3, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 6, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 6, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 4, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 2, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 5, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 1, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 3, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 8, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 10, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 6, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 9, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 7, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 7, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 3, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 7, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 1, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 9, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 5, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 6, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 2, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 10, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 4, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 8, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 8, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 2, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 1, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 8, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 6, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 7, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 4, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 5, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 3, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 10, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 9, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 9, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 10, 0, 1, 1, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 1⟩),
  (⟨1, 0, 5, 0, 1, 6, 0, 0, 6⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 2⟩),
  (⟨1, 0, 7, 0, 1, 4, 0, 0, 4⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 3⟩),
  (⟨1, 0, 8, 0, 1, 3, 0, 0, 3⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 4⟩),
  (⟨1, 0, 2, 0, 1, 9, 0, 0, 9⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 5⟩),
  (⟨1, 0, 9, 0, 1, 2, 0, 0, 2⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 6⟩),
  (⟨1, 0, 3, 0, 1, 8, 0, 0, 8⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 7⟩),
  (⟨1, 0, 4, 0, 1, 7, 0, 0, 7⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 8⟩),
  (⟨1, 0, 6, 0, 1, 5, 0, 0, 5⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 9⟩),
  (⟨1, 0, 1, 0, 1, 10, 0, 0, 10⟩, ⟨1, 0, 1, 0, 1, 10, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 10, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 5, 0, 0, 6⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 1, 7, 0, 0, 4⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 1, 8, 0, 0, 3⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 1, 2, 0, 0, 9⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 1, 9, 0, 0, 2⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 1, 3, 0, 0, 8⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 1, 4, 0, 0, 7⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 1, 6, 0, 0, 5⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 1, 1, 0, 0, 10⟩, ⟨1, 0, 0, 0, 1, 1, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩)]

def T4data : List (Mat × Mat) := [
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 6, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 4, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 3, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 3, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 4, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 9, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 5, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 2, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 6, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 8, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 7, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 7, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 8, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 5, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 9, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 2⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 4⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 3⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 3⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 4⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 9⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 5⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 6⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 8⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 7⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 7⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 8⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 5⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 9⟩),
  (⟨1, 0, 0, 0, 10, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 10, 0, 0, 0, 10⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩)]

def O1 : List Nat := [25, 32, 35, 52, 61, 71, 73, 83, 92, 109, 112, 119]

def rest1 : List Nat := [35, 37, 39, 40, 41, 42, 46, 49, 52, 53, 54, 59, 61, 62, 63, 65, 68, 70, 71, 73, 74, 76, 81, 83, 85, 86, 87, 90, 93, 94, 95, 97, 98, 101, 103, 104, 106, 109, 112, 115, 116, 117, 119]

def O2 : List Nat := [26, 28, 29, 31, 39, 43, 46, 51, 63, 65, 68, 69, 75, 76, 79, 81, 93, 98, 101, 105, 113, 115, 116, 118]

def rest2 : List Nat := [38, 41, 42, 43, 46, 47, 49, 50, 51, 53, 58, 62, 63, 64, 68, 69, 74, 75, 76, 79, 82, 86, 87, 90, 91, 94, 95, 97, 98, 101, 104, 105, 107, 113, 115, 117, 118]

def O3 : List Nat := [27, 30, 38, 40, 41, 50, 53, 54, 57, 58, 64, 70, 74, 80, 86, 87, 90, 91, 94, 103, 104, 106, 114, 117]

def rest3 : List Nat := [37, 40, 41, 47, 50, 53, 57, 58, 59, 64, 74, 85, 86, 87, 90, 91, 94, 102, 103, 106, 107, 117]

def O4 : List Nat := [37, 42, 47, 49, 59, 62, 82, 85, 95, 97, 102, 107]

def rest4 : List Nat := [47, 49, 82, 85, 97, 102, 107]

def gData : List (Nat × Mat × Mat) := [
  (25, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (32, ⟨10, 1, 0, 0, 1, 0, 0, 1, 10⟩, ⟨10, 1, 0, 0, 1, 0, 0, 1, 10⟩),
  (35, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩),
  (52, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩),
  (61, ⟨0, 1, 0, 0, 1, 10, 10, 1, 0⟩, ⟨1, 0, 10, 1, 0, 0, 1, 10, 0⟩),
  (71, ⟨0, 0, 1, 0, 10, 1, 10, 0, 1⟩, ⟨1, 0, 10, 1, 10, 0, 1, 0, 0⟩),
  (73, ⟨10, 0, 1, 0, 10, 1, 0, 0, 1⟩, ⟨10, 0, 1, 0, 10, 1, 0, 0, 1⟩),
  (83, ⟨10, 1, 0, 0, 1, 10, 0, 1, 0⟩, ⟨10, 0, 1, 0, 0, 1, 0, 10, 1⟩),
  (92, ⟨0, 0, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 0, 1, 0, 1, 0, 0⟩),
  (109, ⟨0, 1, 10, 0, 1, 0, 10, 1, 0⟩, ⟨0, 1, 10, 0, 1, 0, 10, 1, 0⟩),
  (112, ⟨10, 0, 1, 0, 0, 1, 0, 10, 1⟩, ⟨10, 1, 0, 0, 1, 10, 0, 1, 0⟩),
  (119, ⟨0, 10, 1, 0, 0, 1, 10, 0, 1⟩, ⟨0, 1, 10, 10, 1, 0, 0, 1, 0⟩),
  (26, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (28, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩),
  (29, ⟨0, 1, 10, 10, 1, 0, 0, 1, 0⟩, ⟨0, 10, 1, 0, 0, 1, 10, 0, 1⟩),
  (31, ⟨10, 1, 0, 0, 1, 0, 0, 1, 10⟩, ⟨10, 1, 0, 0, 1, 0, 0, 1, 10⟩),
  (39, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩),
  (43, ⟨0, 0, 1, 10, 0, 1, 0, 10, 1⟩, ⟨1, 10, 0, 1, 0, 10, 1, 0, 0⟩),
  (46, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩),
  (51, ⟨0, 0, 1, 0, 10, 1, 10, 0, 1⟩, ⟨1, 0, 10, 1, 10, 0, 1, 0, 0⟩),
  (63, ⟨10, 1, 0, 0, 1, 10, 0, 1, 0⟩, ⟨10, 0, 1, 0, 0, 1, 0, 10, 1⟩),
  (65, ⟨0, 10, 1, 0, 0, 1, 10, 0, 1⟩, ⟨0, 1, 10, 10, 1, 0, 0, 1, 0⟩),
  (68, ⟨0, 1, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 0, 1, 0, 0, 0, 0, 1⟩),
  (69, ⟨0, 0, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 0, 1, 0, 1, 0, 0⟩),
  (75, ⟨1, 0, 10, 1, 10, 0, 1, 0, 0⟩, ⟨0, 0, 1, 0, 10, 1, 10, 0, 1⟩),
  (76, ⟨1, 10, 0, 1, 0, 0, 1, 0, 10⟩, ⟨0, 1, 0, 10, 1, 0, 0, 1, 10⟩),
  (79, ⟨0, 10, 1, 10, 0, 1, 0, 0, 1⟩, ⟨0, 10, 1, 10, 0, 1, 0, 0, 1⟩),
  (81, ⟨0, 1, 0, 0, 1, 10, 10, 1, 0⟩, ⟨1, 0, 10, 1, 0, 0, 1, 10, 0⟩),
  (93, ⟨10, 0, 1, 0, 10, 1, 0, 0, 1⟩, ⟨10, 0, 1, 0, 10, 1, 0, 0, 1⟩),
  (98, ⟨1, 0, 0, 1, 0, 10, 1, 10, 0⟩, ⟨1, 0, 0, 1, 0, 10, 1, 10, 0⟩),
  (101, ⟨10, 0, 1, 0, 0, 1, 0, 10, 1⟩, ⟨10, 1, 0, 0, 1, 10, 0, 1, 0⟩),
  (105, ⟨1, 10, 0, 1, 0, 10, 1, 0, 0⟩, ⟨0, 0, 1, 10, 0, 1, 0, 10, 1⟩),
  (113, ⟨0, 1, 0, 10, 1, 0, 0, 1, 10⟩, ⟨1, 10, 0, 1, 0, 0, 1, 0, 10⟩),
  (115, ⟨0, 1, 10, 0, 1, 0, 10, 1, 0⟩, ⟨0, 1, 10, 0, 1, 0, 10, 1, 0⟩),
  (116, ⟨1, 0, 10, 1, 0, 0, 1, 10, 0⟩, ⟨0, 1, 0, 0, 1, 10, 10, 1, 0⟩),
  (118, ⟨1, 0, 0, 1, 10, 0, 1, 0, 10⟩, ⟨1, 0, 0, 1, 10, 0, 1, 0, 10⟩),
  (27, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (30, ⟨10, 1, 0, 0, 1, 0, 0, 1, 10⟩, ⟨10, 1, 0, 0, 1, 0, 0, 1, 10⟩),
  (38, ⟨1, 10, 0, 1, 0, 10, 1, 0, 0⟩, ⟨0, 0, 1, 10, 0, 1, 0, 10, 1⟩),
  (40, ⟨0, 1, 10, 0, 1, 0, 10, 1, 0⟩, ⟨0, 1, 10, 0, 1, 0, 10, 1, 0⟩),
  (41, ⟨0, 0, 1, 0, 10, 1, 10, 0, 1⟩, ⟨1, 0, 10, 1, 10, 0, 1, 0, 0⟩),
  (50, ⟨1, 0, 10, 1, 0, 0, 1, 10, 0⟩, ⟨0, 1, 0, 0, 1, 10, 10, 1, 0⟩),
  (53, ⟨10, 1, 0, 0, 1, 10, 0, 1, 0⟩, ⟨10, 0, 1, 0, 0, 1, 0, 10, 1⟩),
  (54, ⟨0, 0, 1, 10, 0, 1, 0, 10, 1⟩, ⟨1, 10, 0, 1, 0, 10, 1, 0, 0⟩),
  (57, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩),
  (58, ⟨1, 0, 10, 1, 10, 0, 1, 0, 0⟩, ⟨0, 0, 1, 0, 10, 1, 10, 0, 1⟩),
  (64, ⟨0, 10, 1, 10, 0, 1, 0, 0, 1⟩, ⟨0, 10, 1, 10, 0, 1, 0, 0, 1⟩),
  (70, ⟨1, 10, 0, 1, 0, 0, 1, 0, 10⟩, ⟨0, 1, 0, 10, 1, 0, 0, 1, 10⟩),
  (74, ⟨0, 1, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 0, 1, 0, 0, 0, 0, 1⟩),
  (80, ⟨0, 10, 1, 0, 0, 1, 10, 0, 1⟩, ⟨0, 1, 10, 10, 1, 0, 0, 1, 0⟩),
  (86, ⟨0, 0, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 0, 1, 0, 1, 0, 0⟩),
  (87, ⟨1, 0, 0, 1, 0, 10, 1, 10, 0⟩, ⟨1, 0, 0, 1, 0, 10, 1, 10, 0⟩),
  (90, ⟨10, 0, 1, 0, 0, 1, 0, 10, 1⟩, ⟨10, 1, 0, 0, 1, 10, 0, 1, 0⟩),
  (91, ⟨0, 1, 0, 0, 1, 10, 10, 1, 0⟩, ⟨1, 0, 10, 1, 0, 0, 1, 10, 0⟩),
  (94, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩),
  (103, ⟨10, 0, 1, 0, 10, 1, 0, 0, 1⟩, ⟨10, 0, 1, 0, 10, 1, 0, 0, 1⟩),
  (104, ⟨0, 1, 10, 10, 1, 0, 0, 1, 0⟩, ⟨0, 10, 1, 0, 0, 1, 10, 0, 1⟩),
  (106, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩),
  (114, ⟨0, 1, 0, 10, 1, 0, 0, 1, 10⟩, ⟨1, 10, 0, 1, 0, 0, 1, 0, 10⟩),
  (117, ⟨1, 0, 0, 1, 10, 0, 1, 0, 10⟩, ⟨1, 0, 0, 1, 10, 0, 1, 0, 10⟩),
  (37, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  (42, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩),
  (47, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩),
  (49, ⟨10, 0, 1, 0, 10, 1, 0, 0, 1⟩, ⟨10, 0, 1, 0, 10, 1, 0, 0, 1⟩),
  (59, ⟨10, 1, 0, 0, 1, 10, 0, 1, 0⟩, ⟨10, 0, 1, 0, 0, 1, 0, 10, 1⟩),
  (62, ⟨10, 0, 1, 0, 0, 1, 0, 10, 1⟩, ⟨10, 1, 0, 0, 1, 10, 0, 1, 0⟩),
  (82, ⟨10, 1, 0, 0, 1, 0, 0, 1, 10⟩, ⟨10, 1, 0, 0, 1, 0, 0, 1, 10⟩),
  (85, ⟨0, 1, 0, 0, 1, 10, 10, 1, 0⟩, ⟨1, 0, 10, 1, 0, 0, 1, 10, 0⟩),
  (95, ⟨0, 0, 1, 0, 10, 1, 10, 0, 1⟩, ⟨1, 0, 10, 1, 10, 0, 1, 0, 0⟩),
  (97, ⟨0, 1, 10, 0, 1, 0, 10, 1, 0⟩, ⟨0, 1, 10, 0, 1, 0, 10, 1, 0⟩),
  (102, ⟨0, 0, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 0, 1, 0, 1, 0, 0⟩),
  (107, ⟨0, 10, 1, 0, 0, 1, 10, 0, 1⟩, ⟨0, 1, 10, 10, 1, 0, 0, 1, 0⟩)]

def orbitData : List (List Nat × Mat × Mat) := [
  ([0, 121, 132, 12, 25, 35, 49, 74, 103, 119], ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩),
  ([0, 121, 132, 12, 25, 35, 53, 59, 94, 109], ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩),
  ([0, 121, 132, 12, 25, 41, 54, 73, 86, 94], ⟨7, 0, 5, 0, 0, 10, 0, 5, 4⟩, ⟨8, 7, 0, 0, 3, 9, 0, 10, 0⟩),
  ([0, 121, 132, 12, 25, 41, 70, 95, 109, 119], ⟨8, 0, 3, 0, 0, 1, 0, 7, 4⟩, ⟨7, 1, 0, 0, 1, 8, 0, 1, 0⟩),
  ([0, 121, 132, 12, 25, 46, 70, 85, 93, 117], ⟨1, 0, 0, 0, 0, 3, 0, 2, 0⟩, ⟨1, 0, 0, 0, 0, 6, 0, 4, 0⟩),
  ([0, 121, 132, 12, 25, 52, 71, 83, 109, 112], ⟨2, 0, 10, 0, 2, 1, 0, 0, 2⟩, ⟨6, 0, 3, 0, 6, 8, 0, 0, 6⟩),
  ([0, 121, 132, 12, 25, 53, 65, 68, 85, 104], ⟨7, 0, 5, 0, 0, 9, 0, 1, 3⟩, ⟨8, 9, 0, 0, 7, 1, 0, 5, 0⟩),
  ([0, 121, 132, 12, 26, 41, 49, 69, 90, 105], ⟨9, 0, 3, 0, 7, 7, 0, 0, 2⟩, ⟨5, 0, 9, 0, 8, 5, 0, 0, 6⟩),
  ([0, 121, 132, 12, 26, 42, 50, 69, 79, 117], ⟨2, 0, 10, 0, 8, 5, 0, 0, 3⟩, ⟨6, 0, 2, 0, 7, 3, 0, 0, 4⟩),
  ([0, 121, 132, 12, 26, 42, 82, 98, 101, 113], ⟨2, 0, 10, 0, 0, 10, 0, 10, 10⟩, ⟨6, 5, 0, 0, 1, 10, 0, 10, 0⟩),
  ([0, 121, 132, 12, 26, 43, 62, 79, 91, 104], ⟨7, 0, 5, 0, 10, 10, 0, 0, 4⟩, ⟨8, 0, 1, 0, 10, 8, 0, 0, 3⟩),
  ([0, 121, 132, 12, 26, 49, 63, 76, 79, 97], ⟨6, 0, 6, 0, 6, 3, 0, 0, 4⟩, ⟨2, 0, 8, 0, 2, 4, 0, 0, 3⟩),
  ([0, 121, 132, 12, 27, 57, 74, 86, 94, 106], ⟨3, 0, 9, 0, 8, 7, 0, 0, 5⟩, ⟨4, 0, 6, 0, 7, 10, 0, 0, 9⟩)]

/-! ## Bit-mask machinery -/

/-- Lines through the point `x`, as a bit mask (bit `L` set iff `x` lies on line `L`). -/
def ptl (x : Nat) : Nat := (PL >>> (133 * x)) % 2 ^ 133

def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => f n && allBelow f n

theorem allBelow_spec (f : Nat → Bool) : ∀ n, allBelow f n = true → ∀ x, x < n → f x = true
  | 0, _, x, hx => absurd hx (Nat.not_lt_zero x)
  | n + 1, h, x, hx => by
    simp only [allBelow, Bool.and_eq_true] at h
    by_cases hxn : x = n
    · subst hxn; exact h.1
    · exact allBelow_spec f n h.2 x (by omega)

theorem allBelow_of (f : Nat → Bool) : ∀ n, (∀ x, x < n → f x = true) → allBelow f n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [allBelow, Bool.and_eq_true]
    exact ⟨h n (by omega), allBelow_of f n (fun x hx => h x (by omega))⟩

theorem ptl_check :
    allBelow (fun x => allBelow (fun L => (ptl x).testBit L == incB x L) 133) 133 = true := by
  decide +kernel

theorem ptl_ok {x L : Nat} (hx : x < 133) (hL : L < 133) : (ptl x).testBit L = true ↔ inc x L := by
  have h := allBelow_spec _ 133 (allBelow_spec _ 133 ptl_check x hx) L hL
  rw [beq_iff_eq] at h
  rw [h, inc_iff]

theorem ptl_bound {x L : Nat} (h : (ptl x).testBit L = true) : L < 133 := by
  unfold ptl at h
  rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem ne_zero_of_testBit {n i : Nat} (h : n.testBit i = true) : n ≠ 0 := by
  intro h0; rw [h0, Nat.zero_testBit] at h; exact Bool.false_ne_true h

/-- Fast collinearity test. -/
def colB (p q r : Nat) : Bool := !((ptl p &&& ptl q &&& ptl r) == 0)

theorem col_iff {p q r : Nat} (hp : p < 133) (hq : q < 133) (hr : r < 133) :
    Collinear p q r ↔ colB p q r = true := by
  unfold colB
  rw [Bool.not_eq_true', beq_eq_false_iff_ne]
  constructor
  · rintro ⟨L, hL, h1, h2, h3⟩
    apply ne_zero_of_testBit (i := L)
    rw [Nat.testBit_and, Nat.testBit_and, (ptl_ok hp hL).2 h1, (ptl_ok hq hL).2 h2,
      (ptl_ok hr hL).2 h3]
    rfl
  · intro h
    obtain ⟨L, hL⟩ := Nat.ne_zero_implies_bit_true h
    rw [Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true] at hL
    have hL133 := ptl_bound hL.1.1
    exact ⟨L, hL133, (ptl_ok hp hL133).1 hL.1.1, (ptl_ok hq hL133).1 hL.1.2,
      (ptl_ok hr hL133).1 hL.2⟩

def orMap (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: l => f x ||| orMap f l

theorem orMap_testBit (f : Nat → Nat) (i : Nat) :
    ∀ l, (orMap f l).testBit i = true ↔ ∃ x ∈ l, (f x).testBit i = true
  | [] => by simp [orMap]
  | x :: l => by
    rw [orMap, Nat.testBit_or, Bool.or_eq_true, orMap_testBit f i l]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- Lines through some point of `l`. -/
def linesOf (l : List Nat) : Nat := orMap ptl l

/-- Secant lines of `l` (lines through two distinct points of `l`). -/
def SL (l : List Nat) : Nat :=
  orMap (fun a => orMap (fun b => if a = b then 0 else ptl a &&& ptl b) l) l

theorem SL_testBit (l : List Nat) (i : Nat) : (SL l).testBit i = true ↔
    ∃ a ∈ l, ∃ b ∈ l, a ≠ b ∧ (ptl a).testBit i = true ∧ (ptl b).testBit i = true := by
  unfold SL
  rw [orMap_testBit]
  apply exists_congr; intro a; apply and_congr_right; intro _
  rw [orMap_testBit]
  apply exists_congr; intro b; apply and_congr_right; intro _
  by_cases hab : a = b
  · simp [hab]
  · simp [hab, Nat.testBit_and]

/-- Every point is on the arc or on one of its secants. -/
def complFastAux (s : Nat) (l : List Nat) : Bool :=
  allBelow (fun p => l.contains p || !((ptl p &&& s) == 0)) 133

def complFast (l : List Nat) : Bool := complFastAux (SL l) l

/-- Keep the points `d` of the list that are not on a line of the mask `cU`. -/
def filt (cU : Nat) : List Nat → List Nat
  | [] => []
  | d :: l => if (cU &&& ptl d) == 0 then d :: filt cU l else filt cU l

def allTails (f : Nat → List Nat → Bool) : List Nat → Bool
  | [] => true
  | c :: r => f c r && allTails f r

/-! ## The exhaustive search and its soundness -/

/-- Representative complete 10-arc. -/
def R : List Nat := [0, 121, 132, 12, 25, 35, 49, 74, 103, 119]

def leafOK (l : List Nat) : Bool := !complFast l || orbitData.any (fun t => t.1 == l)

/-- `search k chosen rest`: every way of adding `k` points of `rest` (in list order) to
`chosen`, keeping an arc, gives either an incomplete arc or one of the arcs of
`orbitData`. -/
def search : Nat → List Nat → List Nat → Bool
  | 0, chosen, _ => leafOK chosen
  | k + 1, chosen, rest => allTails (fun c r => Nat.blt r.length k ||
      search k (chosen ++ [c]) (filt (ptl c &&& linesOf chosen) r)) rest

/-- Number of entries of `l` that belong to `S`. -/
def cnt (S : List Nat) : List Nat → Nat
  | [] => 0
  | x :: l => (if x ∈ S then 1 else 0) + cnt S l

theorem cnt_append (S l1 l2 : List Nat) : cnt S (l1 ++ l2) = cnt S l1 + cnt S l2 := by
  induction l1 with
  | nil => simp [cnt]
  | cons x l ih => simp only [List.cons_append, cnt, ih]; omega

theorem cnt_le (S : List Nat) : ∀ l, cnt S l ≤ l.length
  | [] => Nat.le_refl 0
  | x :: l => by have := cnt_le S l; simp only [cnt, List.length_cons]; split <;> omega

theorem cnt_zero (S : List Nat) : ∀ l, (∀ x ∈ l, x ∉ S) → cnt S l = 0
  | [] => fun _ => rfl
  | x :: l => fun h => by
    simp only [cnt, if_neg (h x (by simp)), cnt_zero S l (fun y hy => h y (by simp [hy]))]

theorem cnt_pos (S : List Nat) {x : Nat} : ∀ l, x ∈ l → x ∈ S → 0 < cnt S l
  | [], h, _ => absurd h (by simp)
  | y :: l, h, hx => by
    simp only [cnt]
    rcases List.mem_cons.mp h with rfl | h'
    · rw [if_pos hx]; omega
    · have := cnt_pos S l h' hx; omega

theorem cnt_all (S : List Nat) : ∀ l, (∀ x ∈ l, x ∈ S) → cnt S l = l.length
  | [] => fun _ => rfl
  | x :: l => fun h => by
    simp only [cnt, if_pos (h x (by simp)), cnt_all S l (fun y hy => h y (by simp [hy])),
      List.length_cons]
    omega

theorem cnt_cons_left (a : Nat) (S : List Nat) (ha : a ∉ S) :
    ∀ l, cnt (a :: S) l = cnt S l + cnt [a] l
  | [] => rfl
  | x :: l => by
    have ih := cnt_cons_left a S ha l
    simp only [cnt, ih, List.mem_cons, List.mem_singleton]
    by_cases hx : x = a
    · subst hx; simp [ha]; omega
    · by_cases hs : x ∈ S
      · simp [hx, hs]; omega
      · simp [hx, hs]

theorem cnt_single (a : Nat) : ∀ l : List Nat, l.Nodup → a ∈ l → cnt [a] l = 1
  | [], _, h => absurd h (by simp)
  | x :: l, hn, h => by
    rw [List.nodup_cons] at hn
    simp only [cnt, List.mem_singleton]
    by_cases hx : x = a
    · subst hx; rw [if_pos rfl, cnt_zero _ l (fun y hy hy' => hn.1 (by
        rw [List.mem_singleton] at hy'; exact hy' ▸ hy))]
    · rw [if_neg hx, cnt_single a l hn.2 (by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h)]

theorem cnt_full : ∀ (S l : List Nat), S.Nodup → l.Nodup → (∀ s ∈ S, s ∈ l) →
    cnt S l = S.length
  | [], l, _, _, _ => cnt_zero [] l (fun _ _ h => absurd h (by simp))
  | a :: S, l, hS, hl, h => by
    rw [List.nodup_cons] at hS
    rw [cnt_cons_left a S hS.1, cnt_full S l hS.2 hl (fun s hs => h s (by simp [hs])),
      cnt_single a l hl (h a (by simp)), List.length_cons]

theorem allTails_split (f : Nat → List Nat → Bool) :
    ∀ pre c r, allTails f (pre ++ c :: r) = true → f c r = true
  | [], c, r, h => by simp only [List.nil_append, allTails, Bool.and_eq_true] at h; exact h.1
  | _ :: pre, c, r, h => by
    simp only [List.cons_append, allTails, Bool.and_eq_true] at h
    exact allTails_split f pre c r h.2

theorem split_first (S : List Nat) : ∀ rest : List Nat, (∃ x ∈ rest, x ∈ S) →
    ∃ pre c r, rest = pre ++ c :: r ∧ c ∈ S ∧ ∀ x ∈ pre, x ∉ S
  | [], ⟨_, h, _⟩ => absurd h (by simp)
  | y :: l, ⟨x, hx, hxS⟩ => by
    by_cases hy : y ∈ S
    · exact ⟨[], y, l, rfl, hy, fun _ h => absurd h (by simp)⟩
    · have hx' : x ∈ l := by
        rcases List.mem_cons.mp hx with rfl | h
        · exact absurd hxS hy
        · exact h
      obtain ⟨pre, c, r, e, hc, hpre⟩ := split_first S l ⟨x, hx', hxS⟩
      refine ⟨y :: pre, c, r, by rw [e]; rfl, hc, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | h
      · exact hy
      · exact hpre z h

theorem filt_sublist (m : Nat) : ∀ l, (filt m l).Sublist l
  | [] => List.Sublist.slnil
  | d :: l => by
    unfold filt
    split
    · exact (filt_sublist m l).cons₂ d
    · exact (filt_sublist m l).cons d

theorem mem_filt (m : Nat) {x : Nat} : ∀ l, x ∈ l → (m &&& ptl x) = 0 → x ∈ filt m l
  | [], h, _ => absurd h (by simp)
  | d :: l, h, hx => by
    unfold filt
    rcases List.mem_cons.mp h with rfl | h'
    · rw [if_pos (by rw [hx]; rfl)]; simp
    · split
      · exact List.mem_cons_of_mem _ (mem_filt m l h' hx)
      · exact mem_filt m l h' hx

theorem cnt_filt (S : List Nat) (m : Nat) :
    ∀ l, (∀ x ∈ l, x ∈ S → (m &&& ptl x) = 0) → cnt S (filt m l) = cnt S l
  | [] => fun _ => rfl
  | d :: l => fun h => by
    have ih := cnt_filt S m l (fun x hx => h x (by simp [hx]))
    unfold filt
    by_cases hd : d ∈ S
    · rw [if_pos (by rw [h d (by simp) hd]; rfl)]
      simp only [cnt, ih]
    · split
      · simp only [cnt, ih]
      · simp only [cnt, if_neg hd, ih]; omega

/-- A point of an arc outside `chosen` is not on a line joining a point `c` of the arc to
a point of `chosen`. -/
theorem unblocked {S chosen : List Nat} (hS : IsArc S) (hch : ∀ x ∈ chosen, x ∈ S)
    {c s : Nat} (hc : c ∈ S) (hcc : c ∉ chosen) (hs : s ∈ S) (hsc : s ∉ chosen) (hcs : c ≠ s) :
    (ptl c &&& linesOf chosen &&& ptl s) = 0 := by
  apply Decidable.byContradiction
  intro h
  obtain ⟨L, hL⟩ := Nat.ne_zero_implies_bit_true h
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true] at hL
  obtain ⟨⟨h1, h2⟩, h3⟩ := hL
  unfold linesOf at h2
  obtain ⟨a, ha, h4⟩ := (orMap_testBit _ _ _).1 h2
  have hL133 := ptl_bound h1
  have ha' := hch a ha
  apply hS.2 a ha' c hc s hs (fun e => hcc (e ▸ ha)) (fun e => hsc (e ▸ ha)) hcs
  exact ⟨L, hL133, (ptl_ok (hS.1 a ha') hL133).1 h4, (ptl_ok (hS.1 c hc) hL133).1 h1,
    (ptl_ok (hS.1 s hs) hL133).1 h3⟩

/-- A point of an arc outside `chosen ⊆ arc` is on no secant of `chosen`. -/
theorem unblocked_pair {S chosen : List Nat} (hS : IsArc S) (hch : ∀ x ∈ chosen, x ∈ S)
    {s : Nat} (hs : s ∈ S) (hsc : s ∉ chosen) : (ptl s &&& SL chosen) = 0 := by
  apply Decidable.byContradiction
  intro h
  obtain ⟨L, hL⟩ := Nat.ne_zero_implies_bit_true h
  rw [Nat.testBit_and, Bool.and_eq_true, SL_testBit] at hL
  obtain ⟨h1, a, ha, b, hb, hab, h2, h3⟩ := hL
  have hL133 := ptl_bound h1
  apply hS.2 a (hch a ha) b (hch b hb) s hs hab (fun e => hsc (e ▸ ha)) (fun e => hsc (e ▸ hb))
  exact ⟨L, hL133, (ptl_ok (hS.1 a (hch a ha)) hL133).1 h2,
    (ptl_ok (hS.1 b (hch b hb)) hL133).1 h3, (ptl_ok (hS.1 s hs) hL133).1 h1⟩

theorem complFast_of_complete {S chosen : List Nat} (hS : IsArc S) (hC : IsComplete S)
    (hsub : ∀ x ∈ S, x ∈ chosen) : complFast chosen = true := by
  unfold complFast complFastAux
  generalize hs : SL chosen = s
  have key : ∀ p, p < 133 → (chosen.contains p || !((ptl p &&& s) == 0)) = true := by
    intro p hp
    by_cases hpc : p ∈ chosen
    · rw [List.contains_iff_mem.mpr hpc]; rfl
    · have hpS : p ∉ S := fun h => hpc (hsub p h)
      obtain ⟨q, hq, r, hr, hqr, L, hL, h1, h2, h3⟩ := hC p hp hpS
      have hb : (ptl p &&& s).testBit L = true := by
        rw [Nat.testBit_and, ← hs, (ptl_ok hp hL).2 h3, Bool.true_and, SL_testBit]
        exact ⟨q, hsub q hq, r, hsub r hr, hqr, (ptl_ok (hS.1 q hq) hL).2 h1,
          (ptl_ok (hS.1 r hr) hL).2 h2⟩
      have := ne_zero_of_testBit hb
      rw [Bool.or_eq_true]; right
      rw [Bool.not_eq_true', beq_eq_false_iff_ne]; exact this
  exact allBelow_of _ 133 key

theorem search_sound {S : List Nat} (hS : IsArc S) (hC : IsComplete S) :
    ∀ (k : Nat) (chosen rest : List Nat), search k chosen rest = true →
    (∀ x ∈ chosen, x ∈ S) → rest.Nodup → (∀ x ∈ rest, x ∉ chosen) →
    (∀ s ∈ S, s ∉ chosen → s ∈ rest) → cnt S rest = k →
    ∃ t ∈ orbitData, ∀ x, x ∈ S ↔ x ∈ t.1
  | 0, chosen, rest, h, hch, _, _, hcov, hcnt => by
    have hsub : ∀ s ∈ S, s ∈ chosen := by
      intro s hs
      apply Decidable.byContradiction; intro hsc
      have := cnt_pos S rest (hcov s hs hsc) hs
      omega
    have hcf := complFast_of_complete hS hC hsub
    simp only [search, leafOK, hcf, Bool.not_true, Bool.false_or, List.any_eq_true,
      beq_iff_eq] at h
    obtain ⟨t, ht, he⟩ := h
    exact ⟨t, ht, fun x => ⟨fun hx => he ▸ hsub x hx, fun hx => hch x (he ▸ hx)⟩⟩
  | k + 1, chosen, rest, h, hch, hnd, hdis, hcov, hcnt => by
    obtain ⟨pre, c, r, e, hc, hpre⟩ := split_first S rest (by
      apply Decidable.byContradiction; intro hno
      have := cnt_zero S rest (fun x hx hxS => hno ⟨x, hx, hxS⟩); omega)
    subst e
    have hf := allTails_split _ pre c r h
    have hcntr : cnt S r = k := by
      rw [cnt_append, cnt_zero S pre hpre] at hcnt
      simp only [cnt, if_pos hc] at hcnt
      omega
    have hlen : ¬ (r.length < k) := by have := cnt_le S r; omega
    rw [Bool.or_eq_true, Nat.blt_eq] at hf
    have hs := hf.resolve_left hlen
    have hnd' : (c :: r).Nodup := hnd.sublist (List.sublist_append_right pre (c :: r))
    rw [List.nodup_cons] at hnd'
    have hcch : c ∉ chosen := hdis c (by simp)
    have hblock : ∀ x ∈ r, x ∈ S → (ptl c &&& linesOf chosen &&& ptl x) = 0 := by
      intro x hx hxS
      exact unblocked hS hch hc hcch hxS (hdis x (by simp [hx])) (fun e => hnd'.1 (e ▸ hx))
    apply search_sound hS hC k _ _ hs
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hch x h
      · rw [List.mem_singleton] at h; exact h ▸ hc
    · exact hnd'.2.sublist (filt_sublist _ r)
    · intro x hx hx'
      have hxr := (filt_sublist _ r).subset hx
      rcases List.mem_append.mp hx' with h | h
      · exact hdis x (by simp [hxr]) h
      · rw [List.mem_singleton] at h; exact hnd'.1 (h ▸ hxr)
    · intro s hs hsc
      have hs1 : s ∉ chosen := fun h => hsc (List.mem_append_left _ h)
      have hs2 : s ≠ c := fun h => hsc (List.mem_append_right _ (by simp [h]))
      have hsr : s ∈ r := by
        have := hcov s hs hs1
        rcases List.mem_append.mp this with h | h
        · exact absurd hs (hpre s h)
        · rcases List.mem_cons.mp h with h | h
          · exact absurd h hs2
          · exact h
      exact mem_filt _ r hsr (hblock s hsr hs)
    · rw [cnt_filt S _ r hblock, hcntr]

theorem search_root {S : List Nat} (hS : IsCompleteArc 10 S) (chosen rest : List Nat)
    (hsearch : search 5 chosen rest = true) (hcn : chosen.Nodup) (hcl : chosen.length = 5)
    (hch : ∀ x ∈ chosen, x ∈ S) (hnd : rest.Nodup) (hdis : ∀ x ∈ rest, x ∉ chosen)
    (hcov : ∀ s ∈ S, s ∉ chosen → s ∈ rest) : ∃ t ∈ orbitData, ∀ x, x ∈ S ↔ x ∈ t.1 := by
  obtain ⟨hSn, hSl, hSa, hSc⟩ := hS
  apply search_sound hSa hSc 5 chosen rest hsearch hch hnd hdis hcov
  have hnd2 : (chosen ++ rest).Nodup :=
    List.pairwise_append.mpr ⟨hcn, hnd, fun a ha b hb e => hdis b hb (e ▸ ha)⟩
  have hall : ∀ s ∈ S, s ∈ chosen ++ rest := by
    intro s hs
    by_cases h : s ∈ chosen
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (hcov s hs h)
  have h1 := cnt_full S _ hSn hnd2 hall
  rw [cnt_append, cnt_all S chosen hch, hcl, hSl] at h1
  omega

/-! ## Images of arcs under projectivities -/

theorem nodup_map_inj (f : Nat → Nat) : ∀ (l : List Nat), l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hn, hi => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_inj f l hn.2 (fun x hx y hy =>
      hi x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    have := hi b (List.mem_cons_of_mem _ hb) a (by simp) hfb
    exact hn.1 (this ▸ hb)

theorem map_complete {M N : Mat} (h : IsInv M N) {k : Nat} {A : List Nat}
    (hA : IsCompleteArc k A) : IsCompleteArc k (A.map (act M)) := by
  obtain ⟨hnd, hlen, ⟨hb, harc⟩, hc⟩ := hA
  refine ⟨nodup_map_inj _ A hnd (fun x hx y hy e => act_inj h (hb x hx) (hb y hy) e),
    by rw [List.length_map, hlen], ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
    exact act_lt _ _
  · intro p hp q hq r hr hpq hpr hqr hcol
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hq
    obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hr
    exact harc a ha b hb' c hc' (fun e => hpq (e ▸ rfl)) (fun e => hpr (e ▸ rfl))
      (fun e => hqr (e ▸ rfl)) (collinear_of_act h (hb a ha) (hb b hb') (hb c hc') hcol)
  · intro p hp hpA
    have hpinv := act_inv (isInv_symm h) hp
    have hq : act N p ∉ A := fun hmem => hpA (List.mem_map.mpr ⟨_, hmem, hpinv⟩)
    obtain ⟨q, hq, r, hr, hqr, hcol⟩ := hc (act N p) (act_lt _ _) hq
    refine ⟨act M q, List.mem_map.mpr ⟨q, hq, rfl⟩, act M r, List.mem_map.mpr ⟨r, hr, rfl⟩,
      fun e => hqr (act_inj h (hb q hq) (hb r hr) e), ?_⟩
    have := collinear_act h (hb q hq) (hb r hr) (act_lt N p) hcol
    rwa [hpinv] at this

theorem mapsOnto_map (M : Mat) (A : List Nat) : MapsOnto M A (A.map (act M)) :=
  fun _ => List.mem_map

theorem mapsOnto_of_check {M : Mat} {A B : List Nat} (h1 : ∀ a ∈ A, act M a ∈ B)
    (h2 : ∀ x ∈ B, ∃ a ∈ A, act M a = x) : MapsOnto M A B :=
  fun x => ⟨h2 x, fun ⟨a, ha, e⟩ => e ▸ h1 a ha⟩

theorem mapsOnto_comp {M1 N1 M2 : Mat} {A B C : List Nat} (h : mmul N1 M1 = one)
    (hA : ∀ a ∈ A, a < 133) (h1 : MapsOnto M1 A B) (h2 : MapsOnto M2 B C) :
    MapsOnto (mmul M2 M1) A C := by
  intro x
  rw [h2 x]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (h1 b).1 hb
    exact ⟨a, ha, (act_comp M2 h (hA a ha)).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨act M1 a, (h1 _).2 ⟨a, ha, rfl⟩, act_comp M2 h (hA a ha)⟩

theorem mapsOnto_symm {M N : Mat} {A B : List Nat} (h : IsInv M N) (hA : ∀ a ∈ A, a < 133)
    (h1 : MapsOnto M A B) : MapsOnto N B A := by
  intro x
  constructor
  · intro hx
    exact ⟨act M x, (h1 _).2 ⟨x, hx, rfl⟩, act_inv h (hA x hx)⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (h1 b).1 hb
    rw [act_inv h (hA a ha)]; exact ha

theorem mapsOnto_congr_left {M : Mat} {A A' B : List Nat} (h : ∀ x, x ∈ A ↔ x ∈ A')
    (h1 : MapsOnto M A' B) : MapsOnto M A B := fun x => by
  rw [h1 x]
  exact ⟨fun ⟨a, ha, e⟩ => ⟨a, (h a).2 ha, e⟩, fun ⟨a, ha, e⟩ => ⟨a, (h a).1 ha, e⟩⟩

/-! ## Certificates checked by the kernel -/

instance (M N : Mat) : Decidable (IsInv M N) := by unfold IsInv; infer_instance

def frame : List Nat := [0, 121, 132, 12]

theorem frame_lt : ∀ x ∈ frame, x < 133 := by decide

/-- Each of the arcs found by the search is mapped onto `R` by an explicit invertible
matrix. -/
theorem orbit_ok : ∀ t ∈ orbitData, IsInv t.2.1 t.2.2 ∧ (∀ a ∈ t.1, act t.2.1 a ∈ R) ∧
    (∀ x ∈ R, ∃ a ∈ t.1, act t.2.1 a = x) := by decide +kernel

/-- The frame stabiliser data: `e = (c, M, M⁻¹)` with `M c = r`, `M` permuting the frame,
and `M⁻¹` preserving the excluded points `X`. -/
def GOK (X : List Nat) (r c : Nat) (e : Nat × Mat × Mat) : Prop :=
  e.1 = c ∧ IsInv e.2.1 e.2.2 ∧ act e.2.1 c = r ∧
    (∀ f ∈ frame, act e.2.1 f ∈ frame ∧ act e.2.2 f ∈ frame) ∧ (∀ y ∈ X, act e.2.2 y ∈ X)

instance (X : List Nat) (r c : Nat) (e : Nat × Mat × Mat) : Decidable (GOK X r c e) := by
  unfold GOK; infer_instance

theorem reduce (O X rest : List Nat) (r : Nat)
    (hg : ∀ c ∈ O, ∃ e ∈ gData, GOK X r c e)
    (hchn : (frame ++ [r]).Nodup)
    (hrest : rest.Nodup ∧ ∀ x ∈ rest, x ∉ frame ++ [r])
    (hcover : ∀ s, s < 133 → s ∉ frame ++ [r] → s ∉ X → (ptl s &&& SL (frame ++ [r])) = 0 →
      s ∈ rest)
    (hsearch : search 5 (frame ++ [r]) rest = true)
    (S : List Nat) (hS : IsCompleteArc 10 S) (hF : ∀ f ∈ frame, f ∈ S)
    (hO : ∃ c ∈ O, c ∈ S) (hX : ∀ y ∈ X, y ∉ S) :
    ∃ M N, IsInv M N ∧ MapsOnto M S R := by
  obtain ⟨c, hcO, hcS⟩ := hO
  obtain ⟨⟨c', M, N⟩, -, rfl, hinv, hcr, hfr, hXinv⟩ := hg c hcO
  have hb := hS.2.2.1.1
  have hS' := map_complete hinv hS
  have hch : ∀ x ∈ frame ++ [r], x ∈ S.map (act M) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hxb : x < 133 := frame_lt x hx
      exact List.mem_map.mpr ⟨act N x, hF _ (hfr x hx).2, act_inv (isInv_symm hinv) hxb⟩
    · rw [List.mem_singleton] at hx
      exact List.mem_map.mpr ⟨c', hcS, hx ▸ hcr⟩
  have hX' : ∀ y ∈ X, y ∉ S.map (act M) := by
    intro y hy hyS
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hyS
    have := hXinv _ hy
    rw [act_inv hinv (hb s hs)] at this
    exact hX s this hs
  have hcov : ∀ s ∈ S.map (act M), s ∉ frame ++ [r] → s ∈ rest := by
    intro s hs hsc
    exact hcover s (hS'.2.2.1.1 s hs) hsc (fun h => hX' s h hs)
      (unblocked_pair hS'.2.2.1 hch hs hsc)
  obtain ⟨t, ht, hsame⟩ :=
    search_root hS' (frame ++ [r]) rest hsearch hchn rfl hch hrest.1 hrest.2 hcov
  obtain ⟨hWinv, hW1, hW2⟩ := orbit_ok t ht
  have hW : MapsOnto t.2.1 (S.map (act M)) R :=
    mapsOnto_congr_left hsame (mapsOnto_of_check hW1 hW2)
  exact ⟨_, _, isInv_comp hinv hWinv, mapsOnto_comp hinv.2 hb (mapsOnto_map M S) hW⟩

theorem g1ok : ∀ c ∈ O1, ∃ e ∈ gData, GOK [] 25 c e := by decide +kernel
theorem g2ok : ∀ c ∈ O2, ∃ e ∈ gData, GOK O1 26 c e := by decide +kernel
theorem g3ok : ∀ c ∈ O3, ∃ e ∈ gData, GOK (O1 ++ O2) 27 c e := by decide +kernel
theorem g4ok : ∀ c ∈ O4, ∃ e ∈ gData, GOK (O1 ++ O2 ++ O3) 37 c e := by decide +kernel

theorem rest_ok :
    ((frame ++ [25]).Nodup ∧ rest1.Nodup ∧ ∀ x ∈ rest1, x ∉ frame ++ [25]) ∧
    ((frame ++ [26]).Nodup ∧ rest2.Nodup ∧ ∀ x ∈ rest2, x ∉ frame ++ [26]) ∧
    ((frame ++ [27]).Nodup ∧ rest3.Nodup ∧ ∀ x ∈ rest3, x ∉ frame ++ [27]) ∧
    ((frame ++ [37]).Nodup ∧ rest4.Nodup ∧ ∀ x ∈ rest4, x ∉ frame ++ [37]) := by decide

theorem cover1 : ∀ s, s < 133 → s ∉ frame ++ [25] → s ∉ ([] : List Nat) →
    (ptl s &&& SL (frame ++ [25])) = 0 → s ∈ rest1 := by decide +kernel
theorem cover2 : ∀ s, s < 133 → s ∉ frame ++ [26] → s ∉ O1 →
    (ptl s &&& SL (frame ++ [26])) = 0 → s ∈ rest2 := by decide +kernel
theorem cover3 : ∀ s, s < 133 → s ∉ frame ++ [27] → s ∉ O1 ++ O2 →
    (ptl s &&& SL (frame ++ [27])) = 0 → s ∈ rest3 := by decide +kernel
theorem cover4 : ∀ s, s < 133 → s ∉ frame ++ [37] → s ∉ O1 ++ O2 ++ O3 →
    (ptl s &&& SL (frame ++ [37])) = 0 → s ∈ rest4 := by decide +kernel

/-- The four exhaustive searches (one per orbit of the frame stabiliser on the 72 points
off the sides of the complete quadrangle of the frame). -/
theorem search1 : search 5 (frame ++ [25]) rest1 = true := by decide +kernel
theorem search2 : search 5 (frame ++ [26]) rest2 = true := by decide +kernel
theorem search3 : search 5 (frame ++ [27]) rest3 = true := by decide +kernel
theorem search4 : search 5 (frame ++ [37]) rest4 = true := by decide +kernel

theorem cand_cover' : ∀ s, s < 133 → s ∉ frame → (ptl s &&& SL frame) = 0 →
    s ∈ O1 ++ O2 ++ O3 ++ O4 := by decide +kernel

theorem cand_cover (s : Nat) (h1 : s < 133) (h2 : s ∉ frame) (h3 : (ptl s &&& SL frame) = 0) :
    s ∈ O1 ∨ s ∈ O2 ∨ s ∈ O3 ∨ s ∈ O4 := by
  have := cand_cover' s h1 h2 h3
  simp only [List.mem_append] at this
  rcases this with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- Every complete 10-arc containing the frame is projectively equivalent to `R`. -/
theorem to_rep (S : List Nat) (hS : IsCompleteArc 10 S) (hF : ∀ f ∈ frame, f ∈ S) :
    ∃ M N, IsInv M N ∧ MapsOnto M S R := by
  have hex : ∃ s ∈ S, s ∉ frame := by
    apply Decidable.byContradiction; intro h
    have hall : ∀ s ∈ S, s ∈ frame := fun s hs =>
      Decidable.byContradiction (fun h' => h ⟨s, hs, h'⟩)
    have h1 := cnt_full S frame hS.1 (by decide) hall
    have h2 := cnt_le S frame
    rw [h1, hS.2.1] at h2
    exact absurd h2 (by decide)
  obtain ⟨s, hs, hsf⟩ := hex
  have hsO := cand_cover s (hS.2.2.1.1 s hs) hsf (unblocked_pair hS.2.2.1 hF hs hsf)
  obtain ⟨r1, r2, r3, r4⟩ := rest_ok
  by_cases h1 : ∃ c ∈ O1, c ∈ S
  · exact reduce O1 [] rest1 25 g1ok r1.1 r1.2 cover1 search1 S hS hF h1 (by simp)
  by_cases h2 : ∃ c ∈ O2, c ∈ S
  · exact reduce O2 O1 rest2 26 g2ok r2.1 r2.2 cover2 search2 S hS hF h2
      (fun y hy hyS => h1 ⟨y, hy, hyS⟩)
  by_cases h3 : ∃ c ∈ O3, c ∈ S
  · refine reduce O3 (O1 ++ O2) rest3 27 g3ok r3.1 r3.2 cover3 search3 S hS hF h3 ?_
    intro y hy hyS
    rcases List.mem_append.mp hy with hy | hy
    · exact h1 ⟨y, hy, hyS⟩
    · exact h2 ⟨y, hy, hyS⟩
  · refine reduce O4 (O1 ++ O2 ++ O3) rest4 37 g4ok r4.1 r4.2 cover4 search4 S hS hF ?_ ?_
    · rcases hsO with h | h | h | h
      · exact absurd ⟨s, h, hs⟩ h1
      · exact absurd ⟨s, h, hs⟩ h2
      · exact absurd ⟨s, h, hs⟩ h3
      · exact ⟨s, h, hs⟩
    · intro y hy hyS
      rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_append.mp hy with hy | hy
        · exact h1 ⟨y, hy, hyS⟩
        · exact h2 ⟨y, hy, hyS⟩
      · exact h3 ⟨y, hy, hyS⟩

/-! ## The frame lemma: every complete 10-arc can be moved onto the standard frame -/

def t1 (p : Nat) : Mat × Mat := T1data.getD p (one, one)
def t2 (p : Nat) : Mat × Mat := T2data.getD p (one, one)
def t3 (p : Nat) : Mat × Mat := T3data.getD p (one, one)
def t4 (p : Nat) : Mat × Mat := T4data.getD p (one, one)

/-- `t1 p` sends `p` to `e₁ = (1,0,0)` (point `0`). -/
theorem T1ok : ∀ p, p < 133 → IsInv (t1 p).1 (t1 p).2 ∧ act (t1 p).1 p = 0 := by
  decide +kernel

/-- `t2 p` fixes `e₁` and sends `p ≠ e₁` to `e₂ = (0,1,0)` (point `121`). -/
theorem T2ok : ∀ p, p < 133 → p ≠ 0 →
    IsInv (t2 p).1 (t2 p).2 ∧ act (t2 p).1 0 = 0 ∧ act (t2 p).1 p = 121 := by
  decide +kernel

/-- `t3 p` fixes `e₁, e₂` and sends `p ∉ e₁e₂` to `e₃ = (0,0,1)` (point `132`). -/
theorem T3ok : ∀ p, p < 133 → colB 0 121 p = false →
    IsInv (t3 p).1 (t3 p).2 ∧ act (t3 p).1 0 = 0 ∧ act (t3 p).1 121 = 121 ∧
      act (t3 p).1 p = 132 := by
  decide +kernel

/-- `t4 p` fixes `e₁, e₂, e₃` and sends `p` (off the triangle) to `(1,1,1)` (point `12`). -/
theorem T4ok : ∀ p, p < 133 →
    (colB 0 121 p = false ∧ colB 0 132 p = false ∧ colB 121 132 p = false) →
    IsInv (t4 p).1 (t4 p).2 ∧ act (t4 p).1 0 = 0 ∧ act (t4 p).1 121 = 121 ∧
      act (t4 p).1 132 = 132 ∧ act (t4 p).1 p = 12 := by
  decide +kernel

theorem noncol_of {M N : Mat} (h : IsInv M N) {a b c : Nat} (ha : a < 133) (hb : b < 133)
    (hc : c < 133) (hn : ¬ Collinear a b c) {x y : Nat} (hx : act M a = x) (hy : act M b = y)
    (hx' : x < 133) (hy' : y < 133) : colB x y (act M c) = false := by
  cases hcb : colB x y (act M c)
  · rfl
  · exfalso
    apply hn
    rw [← col_iff hx' hy' (act_lt _ _), ← hx, ← hy] at hcb
    exact collinear_of_act h ha hb hc hcb

theorem frame_lemma (A : List Nat) (hA : IsCompleteArc 10 A) :
    ∃ M N, IsInv M N ∧ ∀ f ∈ frame, f ∈ A.map (act M) := by
  obtain ⟨hnd, hlen, ⟨hb, harc⟩, _⟩ := hA
  match A, hnd, hlen, hb, harc with
  | a0 :: a1 :: a2 :: a3 :: tl, hnd, _, hb, harc =>
    have m0 : a0 ∈ a0 :: a1 :: a2 :: a3 :: tl := by simp
    have m1 : a1 ∈ a0 :: a1 :: a2 :: a3 :: tl := by simp
    have m2 : a2 ∈ a0 :: a1 :: a2 :: a3 :: tl := by simp
    have m3 : a3 ∈ a0 :: a1 :: a2 :: a3 :: tl := by simp
    have b0 := hb a0 m0
    have b1 := hb a1 m1
    have b2 := hb a2 m2
    have b3 := hb a3 m3
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨d01, d02, d03, -⟩, ⟨d12, d13, -⟩, ⟨d23, -⟩, -⟩ := hnd
    -- step 1: a0 ↦ e₁
    rcases e1 : t1 a0 with ⟨M1, N1⟩
    have k1 := T1ok a0 b0
    rw [e1] at k1
    obtain ⟨i1, f1⟩ := k1
    -- step 2: a1 ↦ e₂
    have hx1 : act M1 a1 ≠ 0 := fun h => d01 (act_inj i1 b0 b1 (by rw [f1, h]))
    rcases e2 : t2 (act M1 a1) with ⟨M2, N2⟩
    have k2 := T2ok _ (act_lt _ _) hx1
    rw [e2] at k2
    obtain ⟨i2, f2a, f2b⟩ := k2
    have iG2 := isInv_comp i1 i2
    have g2a : act (mmul M2 M1) a0 = 0 := by rw [← act_comp _ i1.2 b0, f1, f2a]
    have g2b : act (mmul M2 M1) a1 = 121 := by rw [← act_comp _ i1.2 b1, f2b]
    -- step 3: a2 ↦ e₃
    have c3 := noncol_of iG2 b0 b1 b2 (harc a0 m0 a1 m1 a2 m2 d01 d02 d12) g2a g2b
      (by decide) (by decide)
    rcases e3 : t3 (act (mmul M2 M1) a2) with ⟨M3, N3⟩
    have k3 := T3ok _ (act_lt _ _) c3
    rw [e3] at k3
    obtain ⟨i3, f3a, f3b, f3c⟩ := k3
    have iG3 := isInv_comp iG2 i3
    have g3a : act (mmul M3 (mmul M2 M1)) a0 = 0 := by rw [← act_comp _ iG2.2 b0, g2a, f3a]
    have g3b : act (mmul M3 (mmul M2 M1)) a1 = 121 := by
      rw [← act_comp _ iG2.2 b1, g2b, f3b]
    have g3c : act (mmul M3 (mmul M2 M1)) a2 = 132 := by rw [← act_comp _ iG2.2 b2, f3c]
    -- step 4: a3 ↦ (1,1,1)
    have c4a := noncol_of iG3 b0 b1 b3 (harc a0 m0 a1 m1 a3 m3 d01 d03 d13) g3a g3b
      (by decide) (by decide)
    have c4b := noncol_of iG3 b0 b2 b3 (harc a0 m0 a2 m2 a3 m3 d02 d03 d23) g3a g3c
      (by decide) (by decide)
    have c4c := noncol_of iG3 b1 b2 b3 (harc a1 m1 a2 m2 a3 m3 d12 d13 d23) g3b g3c
      (by decide) (by decide)
    rcases e4 : t4 (act (mmul M3 (mmul M2 M1)) a3) with ⟨M4, N4⟩
    have k4 := T4ok _ (act_lt _ _) ⟨c4a, c4b, c4c⟩
    rw [e4] at k4
    obtain ⟨i4, f4a, f4b, f4c, f4d⟩ := k4
    have iG4 := isInv_comp iG3 i4
    refine ⟨_, _, iG4, ?_⟩
    intro f hf
    simp only [frame, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact List.mem_map.mpr ⟨a0, m0, by rw [← act_comp _ iG3.2 b0, g3a, f4a]⟩
    · exact List.mem_map.mpr ⟨a1, m1, by rw [← act_comp _ iG3.2 b1, g3b, f4b]⟩
    · exact List.mem_map.mpr ⟨a2, m2, by rw [← act_comp _ iG3.2 b2, g3c, f4c]⟩
    · exact List.mem_map.mpr ⟨a3, m3, by rw [← act_comp _ iG3.2 b3, f4d]⟩

/-! ## Main theorem -/

/-- Any two complete 10-arcs of `PG(2,11)` are projectively equivalent. -/
theorem complete10_equiv (A B : List Nat) (hA : IsCompleteArc 10 A) (hB : IsCompleteArc 10 B) :
    ProjEquiv A B := by
  obtain ⟨M, N, hMN, hF⟩ := frame_lemma A hA
  obtain ⟨W, W', hW, hWR⟩ := to_rep _ (map_complete hMN hA) hF
  obtain ⟨M2, N2, hMN2, hF2⟩ := frame_lemma B hB
  obtain ⟨V2, V2', hV, hVR⟩ := to_rep _ (map_complete hMN2 hB) hF2
  have hAb := hA.2.2.1.1
  have hBb := hB.2.2.1.1
  have h1 : MapsOnto (mmul W M) A R := mapsOnto_comp hMN.2 hAb (mapsOnto_map M A) hWR
  have h2 : MapsOnto (mmul V2 M2) B R := mapsOnto_comp hMN2.2 hBb (mapsOnto_map M2 B) hVR
  have i1 := isInv_comp hMN hW
  have i2 := isInv_comp hMN2 hV
  have h3 := mapsOnto_symm i2 hBb h2
  exact ⟨_, _, isInv_comp i1 (isInv_symm i2), mapsOnto_comp i1.2 hAb h1 h3⟩

theorem complete_of_complFast {l : List Nat} (hb : ∀ x ∈ l, x < 133)
    (h : complFast l = true) : IsComplete l := by
  intro p hp hpl
  unfold complFast complFastAux at h
  have hp' := allBelow_spec _ 133 h p hp
  have hc : l.contains p = false := by
    cases hcp : l.contains p
    · rfl
    · exact absurd (List.contains_iff_mem.mp hcp) hpl
  rw [hc, Bool.false_or, Bool.not_eq_true', beq_eq_false_iff_ne] at hp'
  obtain ⟨L, hL⟩ := Nat.ne_zero_implies_bit_true hp'
  rw [Nat.testBit_and, Bool.and_eq_true, SL_testBit] at hL
  obtain ⟨h1, a, ha, b, hb', hab, h2, h3⟩ := hL
  have hL133 := ptl_bound h1
  exact ⟨a, ha, b, hb', hab, L, hL133, (ptl_ok (hb a ha) hL133).1 h2,
    (ptl_ok (hb b hb') hL133).1 h3, (ptl_ok hp hL133).1 h1⟩

theorem arc_of_colB {l : List Nat} (hb : ∀ x ∈ l, x < 133)
    (h : ∀ p ∈ l, ∀ q ∈ l, ∀ r ∈ l, p ≠ q → p ≠ r → q ≠ r → colB p q r = false) :
    IsArc l := by
  refine ⟨hb, fun p hp q hq r hr hpq hpr hqr hcol => ?_⟩
  rw [col_iff (hb p hp) (hb q hq) (hb r hr), h p hp q hq r hr hpq hpr hqr] at hcol
  exact Bool.false_ne_true hcol

/-- The representative `R = {(1,0,0), (0,1,0), (0,0,1), (1,1,1), (1,2,3), (1,3,2), (1,4,5),
(1,6,8), (1,9,4), (1,10,9)}` is a complete 10-arc. -/
theorem R_complete : IsCompleteArc 10 R := by
  have hb : ∀ x ∈ R, x < 133 := by decide
  refine ⟨by decide, rfl, arc_of_colB hb (by decide +kernel), complete_of_complFast hb ?_⟩
  decide +kernel

/-- Ten points of a conic through the frame: a 10-arc which is *not* complete (the points
`109` and `116` complete it to the conic), so completeness is a genuine restriction. -/
def C10 : List Nat := [0, 121, 132, 12, 25, 42, 62, 68, 81, 93]

theorem C10_not_complete : C10.Nodup ∧ C10.length = 10 ∧ IsArc C10 ∧ ¬ IsComplete C10 := by
  have hb : ∀ x ∈ C10, x < 133 := by decide
  refine ⟨by decide, rfl, arc_of_colB hb (by decide +kernel), fun hc => ?_⟩
  obtain ⟨q, hq, r, hr, hqr, hcol⟩ := hc 109 (by decide) (by decide)
  have key : ∀ q ∈ C10, ∀ r ∈ C10, q ≠ r → colB q r 109 = false := by decide +kernel
  rw [col_iff (hb q hq) (hb r hr) (by decide), key q hq r hr hqr] at hcol
  exact Bool.false_ne_true hcol

/-- **Conjecture 00000001091.** The complete 10-arcs of `PG(2,11)` form exactly one
projective equivalence class: one exists, and any two are projectively equivalent. -/
theorem conjecture_00000001091 :
    (∃ A, IsCompleteArc 10 A) ∧
      ∀ A B, IsCompleteArc 10 A → IsCompleteArc 10 B → ProjEquiv A B :=
  ⟨⟨R, R_complete⟩, complete10_equiv⟩

/-! ## Sanity checks on the model of `PG(2,11)` -/

/-- Every nonzero vector of `F₁₁³` is a nonzero multiple of one of the 133 points. -/
theorem points_cover (v : V) (hv : v ≠ V.zero) :
    ∃ p, p < 133 ∧ ∃ c : F, c ≠ 0 ∧ coord p = smul c v :=
  ⟨idx (norm v), idx_lt _, nscale v, nscale_ne v, coord_idx_norm v hv⟩

/-- Distinct point numbers give non-proportional vectors, and no point is the zero vector. -/
theorem points_distinct {p q : Nat} (hp : p < 133) (hq : q < 133) (c : F) (hc : c ≠ 0)
    (h : coord q = smul c (coord p)) : p = q := by
  have e1 := (coord_ok p hp).2
  have e2 := (coord_ok q hq).2
  rw [h, norm_smul c hc] at e2
  rw [← e1, e2]

theorem coord_ne_zero {p : Nat} (hp : p < 133) : coord p ≠ V.zero := (coord_ok p hp).1

/-- A projectivity maps complete 10-arcs to complete 10-arcs (so `ProjEquiv` really is an
equivalence between complete arcs). -/
theorem image_complete {M N : Mat} (h : IsInv M N) {A : List Nat} (hA : IsCompleteArc 10 A) :
    IsCompleteArc 10 (A.map (act M)) := map_complete h hA

end PG211

#print axioms PG211.conjecture_00000001091
#print axioms PG211.complete10_equiv
#print axioms PG211.R_complete
#print axioms PG211.C10_not_complete
