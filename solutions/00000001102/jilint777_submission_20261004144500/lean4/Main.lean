/-!
# Conjecture 00000001102: peak of Kazhdan–Lusztig R-polynomials

The conjecture claims that for all `x ≤ w` (Bruhat order) in a Coxeter group,
`max R_{x,w} = 2^d · (1 − 2^{−⌈d/2⌉})` with `d = ℓ(w) − ℓ(x)`, where `R_{x,w}` is the
Kazhdan–Lusztig R-polynomial.  We refute this in the symmetric group `S_3`
(Coxeter type `A_2`) under every reasonable reading of "max".

* Permutations of `{1,2,3}` are one-line lists; `S3` lists all six.
* Length `ℓ` = number of inversions; right multiplication by the transposition of
  positions `i, j` swaps two entries.  The reflections of `S_3` are the three
  transpositions.
* Bruhat order `BruhatLe` is defined (inductively) as the reflexive–transitive
  closure of `x → x·t` (`t` a reflection, `ℓ(x) < ℓ(x·t)`); `bruhatB` is a Boolean
  search for such chains, proved equivalent to it on `S_3`.
* Polynomials in `ℤ[q]` are normalized coefficient lists (constant term first).
* `IsRFamily R` is the standard characterization of the R-polynomials:
  `R_{x,w} = 0` unless `x ≤ w`, `R_{w,w} = 1`, and for EVERY simple reflection `s`
  with `ws < w`: `R_{x,w} = R_{xs,ws}` if `xs < x`, else
  `R_{x,w} = (q−1)·R_{x,ws} + q·R_{xs,ws}`.
  We prove that such a family exists (`exists_RFamily`, which also shows the
  recursion is consistent for every choice of descent) and is unique
  (`RFamily_unique`).  Hence all theorems below are about THE R-polynomials.
* `R_classification`: in `S_3`, `R_{x,w}` depends only on `d`:
  `1, q−1, (q−1)², q³−2q²+2q−1` for `d = 0,1,2,3`.
* The conjectured value `2^d(1 − 2^{−c})`, `c = ⌈d/2⌉`, is stated without
  division as `value · 2^c = 2^d · (2^c − 1)`.
* `conjecture_00000001102_false` refutes the clause (even restricted to strict
  pairs `x < w`) for each reading of "max": largest coefficient, largest absolute
  coefficient, sum of absolute coefficients, leading coefficient, degree, number of
  nonzero terms, value at ANY integer point `q₀`, and maximum of `q ↦ R_{x,w}(q)`
  over the integers; also any aggregated reading "max over all pairs with the
  same `d`", and the pair `x = w` refutes every reading `ρ` with `ρ(1) ≠ 0`.
* `literal_recursion_forces_zero`: the garbled recursion
  `R_{x,w} = q R_{xs,w} + R_{x,ws}` of the statement, imposed literally, forces
  `R ≡ 0` (so it cannot define the R-polynomials).
-/

namespace KLR

abbrev Perm := List Nat
abbrev Poly := List Int

/-! ## The symmetric group `S_3` -/

/-- All permutations of `{1,2,3}` in one-line notation. -/
def S3 : List Perm := [[1,2,3], [2,1,3], [1,3,2], [2,3,1], [3,1,2], [3,2,1]]

def e : Perm := [1,2,3]
def s1 : Perm := [2,1,3]
def s1s2 : Perm := [2,3,1]
def w0 : Perm := [3,2,1]

/-- `S3` is exactly the set of permutations of `[1,2,3]` (six distinct ones). -/
theorem S3_spec : S3.Nodup ∧ S3.length = 6 ∧ ∀ x ∈ S3, x.Perm [1,2,3] := by
  refine ⟨by decide, by decide, ?_⟩
  intro x hx
  simp only [S3, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h <;> subst h <;> decide

/-- Right multiplication by the transposition of positions `i` and `j`
(`(w·t)(k) = w(t(k))`): swap the entries in positions `i` and `j`. -/
def swapPos (w : Perm) (i j : Nat) : Perm := (w.set i (w.getD j 0)).set j (w.getD i 0)

/-- Right multiplication by the simple reflection `s_{i+1} = (i, i+1)` (0-based positions). -/
def rmul (w : Perm) (i : Nat) : Perm := swapPos w i (i + 1)

/-- The reflections of `S_3`: all transpositions (as position pairs). -/
def transp : List (Nat × Nat) := [(0,1), (0,2), (1,2)]

/-- Coxeter length in `S_n` = number of inversions. -/
def inv : Perm → Nat
  | [] => 0
  | a :: l => (l.filter (fun b => decide (b < a))).length + inv l

theorem names_ok : s1 = rmul e 0 ∧ s1s2 = rmul (rmul e 0) 1 ∧
    w0 = rmul (rmul (rmul e 0) 1) 0 ∧ inv e = 0 ∧ inv s1 = 1 ∧ inv s1s2 = 2 ∧ inv w0 = 3 := by
  decide

theorem S3_closed_transp : ∀ x ∈ S3, ∀ t ∈ transp, swapPos x t.1 t.2 ∈ S3 := by decide
theorem S3_closed_rmul : ∀ x ∈ S3, ∀ i ∈ [0,1], rmul x i ∈ S3 := by decide
theorem S3_inv_le : ∀ x ∈ S3, inv x ≤ 3 := by decide
/-- The simple reflections are reflections. -/
theorem simple_are_reflections : ∀ i ∈ [0,1], (i, i+1) ∈ transp := by decide

/-! ## Bruhat order -/

/-- Bruhat order: `x ≤ w` iff there is a chain `x = x₀ → x₁ → ⋯ → x_k = w` with
`x_{i+1} = x_i · t_i`, `t_i` a reflection and `ℓ(x_i) < ℓ(x_{i+1})`. -/
inductive BruhatLe : Perm → Perm → Prop
  | refl (x : Perm) : BruhatLe x x
  | step (x w : Perm) (t : Nat × Nat) : t ∈ transp → inv x < inv (swapPos x t.1 t.2) →
      BruhatLe (swapPos x t.1 t.2) w → BruhatLe x w

/-- Bounded search for such a chain. -/
def reach : Nat → Perm → Perm → Bool
  | 0, x, w => x == w
  | n + 1, x, w => x == w || transp.any (fun t =>
      decide (inv x < inv (swapPos x t.1 t.2)) && reach n (swapPos x t.1 t.2) w)

/-- Chains in `S_3` have at most `3` steps (the length increases at each step). -/
def bruhatB (x w : Perm) : Bool := reach 3 x w

theorem reach_sound : ∀ n x w, reach n x w = true → BruhatLe x w := by
  intro n
  induction n with
  | zero =>
    intro x w h
    simp only [reach, beq_iff_eq] at h
    subst h; exact BruhatLe.refl x
  | succ n ih =>
    intro x w h
    simp only [reach, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
    rcases h with h | ⟨t, ht, hlt, hr⟩
    · subst h; exact BruhatLe.refl x
    · exact BruhatLe.step x w t ht hlt (ih _ _ hr)

theorem reach_refl : ∀ n x, reach n x x = true := by
  intro n x; cases n <;> simp [reach]

theorem reach_mono : ∀ n x w, reach n x w = true → reach (n + 1) x w = true := by
  intro n
  induction n with
  | zero =>
    intro x w h
    simp only [reach, beq_iff_eq] at h
    subst h; exact reach_refl _ _
  | succ n ih =>
    intro x w h
    have h' := h
    simp only [reach, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at h'
    rcases h' with h' | ⟨t, ht, hlt, hr⟩
    · subst h'; exact reach_refl _ _
    · show (x == w || transp.any (fun t =>
          decide (inv x < inv (swapPos x t.1 t.2)) && reach (n + 1) (swapPos x t.1 t.2) w)) = true
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨t, ht, hlt, ih _ _ hr⟩

theorem reach_mono_le : ∀ k n x w, reach n x w = true → reach (n + k) x w = true := by
  intro k
  induction k with
  | zero => intro n x w h; exact h
  | succ k ih =>
    intro n x w h
    exact reach_mono _ _ _ (ih n x w h)

theorem reach_complete : ∀ x w, BruhatLe x w → x ∈ S3 → reach (3 - inv x) x w = true := by
  intro x w h
  induction h with
  | refl x => intro _; exact reach_refl _ _
  | step x w t ht hlt _ ih =>
    intro hx
    have hy := S3_closed_transp x hx t ht
    have hr := ih hy
    have h3 := S3_inv_le _ hy
    have hk : 3 - inv x = (3 - inv (swapPos x t.1 t.2) + (inv (swapPos x t.1 t.2) - inv x - 1)) + 1 := by
      omega
    rw [hk]
    show (x == w || transp.any (fun t =>
        decide (inv x < inv (swapPos x t.1 t.2)) && reach _ (swapPos x t.1 t.2) w)) = true
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨t, ht, hlt, reach_mono_le _ _ _ _ hr⟩

/-- `bruhatB` is exactly the Bruhat order on `S_3`. -/
theorem bruhatB_iff (x w : Perm) (hx : x ∈ S3) : bruhatB x w = true ↔ BruhatLe x w := by
  constructor
  · exact reach_sound 3 x w
  · intro h
    have := reach_complete x w h hx
    have h3 := S3_inv_le x hx
    have := reach_mono_le (inv x) _ x w this
    rwa [show 3 - inv x + inv x = 3 by omega] at this

/-- Bruhat order is compatible with length (so `ℓ(w) − ℓ(x)` below is a true difference). -/
theorem bruhat_length : ∀ x ∈ S3, ∀ w ∈ S3, bruhatB x w = true → inv x ≤ inv w := by decide

/-- Non-vacuity: the Bruhat order on `S_3` has `19` comparable pairs `x ≤ w` (of which
`13` are strict); `e ≤ w` for all `w`. -/
theorem bruhat_count :
    ((S3.flatMap fun x => S3.filter fun w => bruhatB x w).length = 19) ∧
    (∀ w ∈ S3, bruhatB e w = true) ∧ bruhatB s1 [1,3,2] = false := by decide

/-! ## Polynomials in `ℤ[q]` (normalized coefficient lists) -/

def addL : Poly → Poly → Poly
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

def mulL : Poly → Poly → Poly
  | [], _ => []
  | a :: l, m => addL (m.map (a * ·)) (0 :: mulL l m)

/-- Drop trailing zero coefficients. -/
def trim (l : Poly) : Poly := (l.reverse.dropWhile (· == 0)).reverse

def padd (a b : Poly) : Poly := trim (addL a b)
def pmul (a b : Poly) : Poly := trim (mulL a b)

/-- `q − 1` and `q`. -/
def qm1 : Poly := [-1, 1]
def qX : Poly := [0, 1]

def evalP (q : Int) : Poly → Int
  | [] => 0
  | a :: l => a + q * evalP q l

/-! ## R-polynomials -/

/-- The defining properties of the Kazhdan–Lusztig R-polynomials of `S_3`. -/
structure IsRFamily (R : Perm → Perm → Poly) : Prop where
  zero : ∀ x ∈ S3, ∀ w ∈ S3, bruhatB x w = false → R x w = []
  diag : ∀ w ∈ S3, R w w = [1]
  step : ∀ x ∈ S3, ∀ w ∈ S3, ∀ i ∈ [0,1], inv (rmul w i) < inv w →
    R x w = if inv (rmul x i) < inv x then R (rmul x i) (rmul w i)
            else padd (pmul qm1 (R x (rmul w i))) (pmul qX (R (rmul x i) (rmul w i)))

def firstDescent (w : Perm) : Option Nat :=
  if inv (rmul w 0) < inv w then some 0 else if inv (rmul w 1) < inv w then some 1 else none

/-- Computation of `R` by the recursion with the first right descent. -/
def Rc : Nat → Perm → Perm → Poly
  | 0, x, w => if x == w then [1] else []
  | n + 1, x, w =>
    if bruhatB x w = false then []
    else if x == w then [1]
    else match firstDescent w with
      | none => []
      | some i =>
        if inv (rmul x i) < inv x then Rc n (rmul x i) (rmul w i)
        else padd (pmul qm1 (Rc n x (rmul w i))) (pmul qX (Rc n (rmul x i) (rmul w i)))

def R0 (x w : Perm) : Poly := Rc 3 x w

/-- Existence (and consistency of the recursion for EVERY choice of descent). -/
theorem R0_isRFamily : IsRFamily R0 where
  zero := by decide
  diag := by decide
  step := by decide

theorem exists_RFamily : ∃ R, IsRFamily R := ⟨R0, R0_isRFamily⟩

theorem S3_e_or_descent : ∀ w ∈ S3, w = e ∨ ∃ i ∈ [0,1], inv (rmul w i) < inv w := by decide
theorem not_le_e : ∀ x ∈ S3, x ≠ e → bruhatB x e = false := by decide

/-- Uniqueness: any two families satisfying the defining properties agree on `S_3`. -/
theorem RFamily_unique (R R' : Perm → Perm → Poly) (h : IsRFamily R) (h' : IsRFamily R') :
    ∀ x ∈ S3, ∀ w ∈ S3, R x w = R' x w := by
  suffices H : ∀ n, ∀ w ∈ S3, inv w ≤ n → ∀ x ∈ S3, R x w = R' x w by
    intro x hx w hw; exact H _ w hw (Nat.le_refl _) x hx
  intro n
  induction n with
  | zero =>
    intro w hw hn x hx
    rcases S3_e_or_descent w hw with he | ⟨i, _, hi⟩
    · subst he
      by_cases hxe : x = e
      · subst hxe; rw [h.diag e hw, h'.diag e hw]
      · rw [h.zero x hx e hw (not_le_e x hx hxe), h'.zero x hx e hw (not_le_e x hx hxe)]
    · omega
  | succ n ih =>
    intro w hw hn x hx
    rcases S3_e_or_descent w hw with he | ⟨i, hi01, hi⟩
    · subst he
      by_cases hxe : x = e
      · subst hxe; rw [h.diag e hw, h'.diag e hw]
      · rw [h.zero x hx e hw (not_le_e x hx hxe), h'.zero x hx e hw (not_le_e x hx hxe)]
    · have hws := S3_closed_rmul w hw i hi01
      have hxs := S3_closed_rmul x hx i hi01
      have hle : inv (rmul w i) ≤ n := by omega
      rw [h.step x hx w hw i hi01 hi, h'.step x hx w hw i hi01 hi,
        ih _ hws hle _ hxs, ih _ hws hle _ hx]

/-- The R-polynomial of `S_3` for each length difference `d`. -/
def Pd : Nat → Poly
  | 0 => [1]
  | 1 => [-1, 1]
  | 2 => [1, -2, 1]
  | _ => [-1, 2, -2, 1]

theorem Pd_values : Pd 1 = qm1 ∧ Pd 2 = pmul qm1 qm1 ∧
    Pd 3 = padd (pmul qm1 (pmul qm1 qm1)) (pmul qX qm1) := by decide

theorem R0_classification : ∀ x ∈ S3, ∀ w ∈ S3, bruhatB x w = true →
    R0 x w = Pd (inv w - inv x) := by decide

/-- Classification of all R-polynomials of `S_3`: `R_{x,w}` depends only on
`d = ℓ(w) − ℓ(x)` and equals `1, q−1, (q−1)², q³−2q²+2q−1` for `d = 0,1,2,3`. -/
theorem R_classification (R : Perm → Perm → Poly) (h : IsRFamily R) :
    ∀ x ∈ S3, ∀ w ∈ S3, bruhatB x w = true → R x w = Pd (inv w - inv x) := by
  intro x hx w hw hb
  rw [RFamily_unique R R0 h R0_isRFamily x hx w hw]
  exact R0_classification x hx w hw hb

theorem R_values (R : Perm → Perm → Poly) (h : IsRFamily R) :
    R e e = [1] ∧ R e s1 = [-1, 1] ∧ R e s1s2 = [1, -2, 1] ∧ R e w0 = [-1, 2, -2, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [RFamily_unique R R0 h R0_isRFamily _ (by decide) _ (by decide)] <;> decide

/-! ## The conjecture and its readings -/

/-- A "reading" of `max R_{x,w}`: a number attached to a polynomial. -/
abbrev Reading := Poly → Int

/-- Largest coefficient. -/
def maxCoeff : Reading
  | [] => 0
  | a :: l => l.foldl max a
/-- Largest absolute value of a coefficient. -/
def maxAbsCoeff : Reading
  | [] => 0
  | a :: l => l.foldl (fun m b => max m (b.natAbs : Int)) (a.natAbs : Int)
/-- Sum of absolute values of the coefficients. -/
def sumAbsCoeff : Reading := fun l => l.foldl (fun s b => s + (b.natAbs : Int)) 0
/-- Leading coefficient. -/
def leadCoeff : Reading := fun l => l.getLastD 0
/-- Degree. -/
def degree : Reading := fun l => (l.length : Int) - 1
/-- Number of nonzero terms. -/
def numTerms : Reading := fun l => ((l.filter (· != 0)).length : Int)
/-- Value at `q = q₀`. -/
def evalAt (q₀ : Int) : Reading := evalP q₀

/-- `c = ⌈d/2⌉`. -/
def ceilHalf (d : Nat) : Nat := (d + 1) / 2

/-- The conjectured identity `v = 2^d (1 − 2^{−⌈d/2⌉})`, multiplied out by `2^{⌈d/2⌉}`. -/
def Formula (v : Int) (d : Nat) : Prop :=
  v * 2 ^ ceilHalf d = 2 ^ d * (2 ^ ceilHalf d - 1)

instance (v : Int) (d : Nat) : Decidable (Formula v d) := by unfold Formula; infer_instance

/-- The conjectured value is the integer `2^d − 2^{⌊d/2⌋}`: `0, 1, 2, 6` for `d = 0..3`. -/
theorem formula_values : Formula 0 0 ∧ Formula 1 1 ∧ Formula 2 2 ∧ Formula 6 3 ∧ Formula 12 4 ∧
    ∀ v : Int, ∀ d < 4, Formula v d → v = 2 ^ d - 2 ^ (d / 2) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro v d hd hf
  unfold Formula ceilHalf at hf
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp at hf ⊢ <;> omega

/-- The conjecture under reading `ρ`: for all `x ≤ w` in `S_3`,
`ρ(R_{x,w}) = 2^d (1 − 2^{−⌈d/2⌉})`, `d = ℓ(w) − ℓ(x)`. -/
def Claim (ρ : Reading) (R : Perm → Perm → Poly) : Prop :=
  ∀ x ∈ S3, ∀ w ∈ S3, bruhatB x w = true → Formula (ρ (R x w)) (inv w - inv x)

/-- The weaker claim restricted to strict pairs `x < w`. -/
def ClaimStrict (ρ : Reading) (R : Perm → Perm → Poly) : Prop :=
  ∀ x ∈ S3, ∀ w ∈ S3, bruhatB x w = true → x ≠ w → Formula (ρ (R x w)) (inv w - inv x)

/-- Reading "maximum of the function `q ↦ R_{x,w}(q)` over the integers". -/
def ClaimMaxValue (R : Perm → Perm → Poly) : Prop :=
  ∀ x ∈ S3, ∀ w ∈ S3, bruhatB x w = true → x ≠ w →
    ∃ m : Int, Formula m (inv w - inv x) ∧ (∃ q, evalP q (R x w) = m) ∧ ∀ q, evalP q (R x w) ≤ m

/-- Aggregated reading: for each `d`, the maximum of `ρ(R_{x,w})` over all strict
pairs with `ℓ(w) − ℓ(x) = d` is attained and equals the formula. -/
def ClaimAgg (ρ : Reading) (R : Perm → Perm → Poly) : Prop :=
  ∀ d, (∃ x ∈ S3, ∃ w ∈ S3, bruhatB x w = true ∧ x ≠ w ∧ inv w - inv x = d) →
    ∃ m : Int, Formula m d ∧
      (∃ x ∈ S3, ∃ w ∈ S3, bruhatB x w = true ∧ x ≠ w ∧ inv w - inv x = d ∧ ρ (R x w) = m) ∧
      (∀ x ∈ S3, ∀ w ∈ S3, bruhatB x w = true → x ≠ w → inv w - inv x = d → ρ (R x w) ≤ m)

theorem claim_imp_strict (ρ : Reading) (R : Perm → Perm → Poly) :
    Claim ρ R → ClaimStrict ρ R := fun h x hx w hw hb _ => h x hx w hw hb

/-- Since `R_{x,w}` depends only on `d` in `S_3`, the aggregated reading implies
the per-pair (strict) reading. -/
theorem agg_imp_strict (ρ : Reading) (R : Perm → Perm → Poly) (h : IsRFamily R) :
    ClaimAgg ρ R → ClaimStrict ρ R := by
  intro hA x hx w hw hb hne
  obtain ⟨m, hm, ⟨x', hx', w', hw', hb', _, hd', hρ⟩, _⟩ := hA _ ⟨x, hx, w, hw, hb, hne, rfl⟩
  rw [R_classification R h x hx w hw hb, ← hd', ← R_classification R h x' hx' w' hw' hb', hρ,
    hd']
  exact hm

/-- Every strict pair of a given `d` has the same R-polynomial, so `ClaimStrict` and
`ClaimAgg` are equivalent; here the direction needed for the disproof. -/
theorem not_agg_of_not_strict (ρ : Reading) (R : Perm → Perm → Poly) (h : IsRFamily R)
    (hn : ¬ ClaimStrict ρ R) : ¬ ClaimAgg ρ R := fun hA => hn (agg_imp_strict ρ R h hA)

/-! ## The refutations -/

section
variable (R : Perm → Perm → Poly) (h : IsRFamily R)
include h

/-- d = 2, `x = e`, `w = s₁s₂`: largest coefficient of `(q−1)²` is `1 ≠ 2`. -/
theorem not_maxCoeff : ¬ ClaimStrict maxCoeff R := by
  intro hc
  have := hc e (by decide) s1s2 (by decide) (by decide) (by decide)
  rw [(R_values R h).2.2.1] at this; revert this; decide

/-- d = 3, `x = e`, `w = w₀`: largest |coefficient| of `q³−2q²+2q−1` is `2 ≠ 6`. -/
theorem not_maxAbsCoeff : ¬ ClaimStrict maxAbsCoeff R := by
  intro hc
  have := hc e (by decide) w0 (by decide) (by decide) (by decide)
  rw [(R_values R h).2.2.2] at this; revert this; decide

/-- d = 1, `x = e`, `w = s₁`: `|−1| + |1| = 2 ≠ 1`. -/
theorem not_sumAbsCoeff : ¬ ClaimStrict sumAbsCoeff R := by
  intro hc
  have := hc e (by decide) s1 (by decide) (by decide) (by decide)
  rw [(R_values R h).2.1] at this; revert this; decide

/-- d = 2: leading coefficient `1 ≠ 2`. -/
theorem not_leadCoeff : ¬ ClaimStrict leadCoeff R := by
  intro hc
  have := hc e (by decide) s1s2 (by decide) (by decide) (by decide)
  rw [(R_values R h).2.2.1] at this; revert this; decide

/-- d = 3: degree `3 ≠ 6`. -/
theorem not_degree : ¬ ClaimStrict degree R := by
  intro hc
  have := hc e (by decide) w0 (by decide) (by decide) (by decide)
  rw [(R_values R h).2.2.2] at this; revert this; decide

/-- d = 1: `q − 1` has `2 ≠ 1` nonzero terms. -/
theorem not_numTerms : ¬ ClaimStrict numTerms R := by
  intro hc
  have := hc e (by decide) s1 (by decide) (by decide) (by decide)
  rw [(R_values R h).2.1] at this; revert this; decide

/-- For every integer `q₀`: d = 1 forces `q₀ − 1 = 1`, i.e. `q₀ = 2`, and then
d = 2 gives `(2−1)² = 1 ≠ 2`. -/
theorem not_evalAt (q₀ : Int) : ¬ ClaimStrict (evalAt q₀) R := by
  intro hc
  have h1 := hc e (by decide) s1 (by decide) (by decide) (by decide)
  have h2 := hc e (by decide) s1s2 (by decide) (by decide) (by decide)
  rw [(R_values R h).2.1, show inv s1 - inv e = 1 by decide] at h1
  rw [(R_values R h).2.2.1, show inv s1s2 - inv e = 2 by decide] at h2
  unfold Formula ceilHalf evalAt evalP evalP evalP at h1
  simp at h1
  have hq : q₀ = 2 := by omega
  subst hq
  revert h2; decide

/-- d = 1: `q ↦ q − 1` is unbounded (its value at `3` is `2 > 1`), so its maximum is not `1`. -/
theorem not_maxValue : ¬ ClaimMaxValue R := by
  intro hc
  obtain ⟨m, hm, _, hle⟩ := hc e (by decide) s1 (by decide) (by decide) (by decide)
  rw [(R_values R h).2.1] at hle
  rw [show inv s1 - inv e = 1 by decide] at hm
  have h3 := hle 3
  unfold Formula ceilHalf at hm
  simp at hm
  simp [evalP] at h3
  omega

/-- The pair `x = w` (d = 0) refutes the non-strict clause for every reading with `ρ(1) ≠ 0`:
`R_{w,w} = 1` but the formula gives `2^0 (1 − 2^0) = 0`. -/
theorem not_claim_diag (ρ : Reading) (hρ : ρ [1] ≠ 0) : ¬ Claim ρ R := by
  intro hc
  have := hc e (by decide) e (by decide) (by decide)
  rw [(R_values R h).1] at this
  simp [Formula, ceilHalf, names_ok] at this
  exact hρ this

end

/-- **Main theorem.** For the (unique) R-polynomials of `S_3`, the conjecture
`max R_{x,w} = 2^d (1 − 2^{−⌈d/2⌉})` fails under every listed reading of "max",
already for strict pairs `x < w`, hence also for all pairs `x ≤ w`, and also in the
aggregated form "max over all pairs with the same `d`". -/
theorem conjecture_00000001102_false (R : Perm → Perm → Poly) (h : IsRFamily R) :
    ¬ Claim maxCoeff R ∧ ¬ Claim maxAbsCoeff R ∧ ¬ Claim sumAbsCoeff R ∧
    ¬ Claim leadCoeff R ∧ ¬ Claim degree R ∧ ¬ Claim numTerms R ∧
    (∀ q₀ : Int, ¬ Claim (evalAt q₀) R) ∧ ¬ ClaimMaxValue R ∧
    ¬ ClaimStrict maxCoeff R ∧ ¬ ClaimStrict maxAbsCoeff R ∧ ¬ ClaimStrict sumAbsCoeff R ∧
    ¬ ClaimStrict leadCoeff R ∧ ¬ ClaimStrict degree R ∧ ¬ ClaimStrict numTerms R ∧
    (∀ q₀ : Int, ¬ ClaimStrict (evalAt q₀) R) ∧
    ¬ ClaimAgg maxCoeff R ∧ ¬ ClaimAgg maxAbsCoeff R ∧ ¬ ClaimAgg sumAbsCoeff R ∧
    ¬ ClaimAgg leadCoeff R ∧ ¬ ClaimAgg degree R ∧ ¬ ClaimAgg numTerms R ∧
    (∀ q₀ : Int, ¬ ClaimAgg (evalAt q₀) R) := by
  have a := not_maxCoeff R h
  have b := not_maxAbsCoeff R h
  have c := not_sumAbsCoeff R h
  have d := not_leadCoeff R h
  have e' := not_degree R h
  have f := not_numTerms R h
  have g := not_evalAt R h
  exact ⟨fun hc => a (claim_imp_strict _ _ hc), fun hc => b (claim_imp_strict _ _ hc),
    fun hc => c (claim_imp_strict _ _ hc), fun hc => d (claim_imp_strict _ _ hc),
    fun hc => e' (claim_imp_strict _ _ hc), fun hc => f (claim_imp_strict _ _ hc),
    fun q₀ hc => g q₀ (claim_imp_strict _ _ hc), not_maxValue R h,
    a, b, c, d, e', f, g,
    not_agg_of_not_strict _ _ h a, not_agg_of_not_strict _ _ h b,
    not_agg_of_not_strict _ _ h c, not_agg_of_not_strict _ _ h d,
    not_agg_of_not_strict _ _ h e', not_agg_of_not_strict _ _ h f,
    fun q₀ => not_agg_of_not_strict _ _ h (g q₀)⟩

/-- The same statement for the concrete family `R0` (non-vacuity: `IsRFamily R0`). -/
theorem conjecture_00000001102_false_R0 :
    IsRFamily R0 ∧ ¬ Claim maxCoeff R0 ∧ ¬ Claim maxAbsCoeff R0 ∧ ¬ Claim sumAbsCoeff R0 ∧
    ¬ Claim leadCoeff R0 ∧ ¬ Claim degree R0 ∧ ¬ Claim numTerms R0 ∧
    (∀ q₀ : Int, ¬ Claim (evalAt q₀) R0) ∧ ¬ ClaimMaxValue R0 :=
  have H := conjecture_00000001102_false R0 R0_isRFamily
  ⟨R0_isRFamily, H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1,
    H.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.1⟩

/-! ## The literal recursion of the statement forces `R ≡ 0`

Polynomials (or even formal power series) are coefficient sequences `ℕ → ℤ`;
multiplication by `q` shifts.  If `m` is right multiplication by one simple
reflection `s` (any involution), and `R_{x,w} = q R_{xs,w} + R_{x,ws}` for all
`x, w`, then every coefficient of every `R_{x,w}` vanishes. -/

theorem literal_recursion_forces_zero {W : Type} (m : W → W) (hm : ∀ x, m (m x) = x)
    (R : W → W → Nat → Int)
    (hR : ∀ x w k, R x w k = (if k = 0 then 0 else R (m x) w (k - 1)) + R x (m w) k) :
    ∀ x w k, R x w k = 0 := by
  -- Step 1: `R_{y,w} = − R_{y,ws}`.
  have hneg : ∀ y w j, R y w j + R y (m w) j = 0 := by
    intro y w j
    have h1 := hR (m y) w (j + 1)
    have h2 := hR (m y) (m w) (j + 1)
    rw [hm] at h1 h2
    rw [hm] at h2
    simp at h1 h2
    omega
  -- Step 2: induction on the degree.
  intro x w k
  induction k generalizing x w with
  | zero =>
    have h1 := hR x w 0
    have h2 := hneg x w 0
    simp at h1
    omega
  | succ k ih =>
    have h1 := hR x w (k + 1)
    have h2 := hneg x w (k + 1)
    simp [ih] at h1
    omega

/-- Consequently, on `S_3` (with `s = s₁`) no family satisfying the literal recursion
can have `R_{e,e} = 1`. -/
theorem literal_recursion_inconsistent :
    ¬ ∃ R : {x : Perm // x ∈ S3} → {x : Perm // x ∈ S3} → Nat → Int,
      (∀ x w k, R x w k = (if k = 0 then 0 else
          R ⟨rmul x.1 0, S3_closed_rmul x.1 x.2 0 (by decide)⟩ w (k - 1)) +
          R x ⟨rmul w.1 0, S3_closed_rmul w.1 w.2 0 (by decide)⟩ k) ∧
      R ⟨e, by decide⟩ ⟨e, by decide⟩ 0 = 1 := by
  rintro ⟨R, hR, h1⟩
  have hm : ∀ x : {x : Perm // x ∈ S3},
      (⟨rmul (rmul x.1 0) 0, S3_closed_rmul _ (S3_closed_rmul x.1 x.2 0 (by decide)) 0 (by decide)⟩ :
        {x : Perm // x ∈ S3}) = x := by
    intro ⟨x, hx⟩
    apply Subtype.ext
    show rmul (rmul x 0) 0 = x
    simp only [S3, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h <;> subst h <;> decide
  have := literal_recursion_forces_zero
    (fun x => ⟨rmul x.1 0, S3_closed_rmul x.1 x.2 0 (by decide)⟩) hm R hR ⟨e, by decide⟩ ⟨e, by decide⟩ 0
  omega

end KLR

#print axioms KLR.S3_spec
#print axioms KLR.bruhatB_iff
#print axioms KLR.bruhat_count
#print axioms KLR.R0_isRFamily
#print axioms KLR.RFamily_unique
#print axioms KLR.R_classification
#print axioms KLR.R_values
#print axioms KLR.formula_values
#print axioms KLR.conjecture_00000001102_false
#print axioms KLR.conjecture_00000001102_false_R0
#print axioms KLR.not_claim_diag
#print axioms KLR.literal_recursion_forces_zero
#print axioms KLR.literal_recursion_inconsistent
