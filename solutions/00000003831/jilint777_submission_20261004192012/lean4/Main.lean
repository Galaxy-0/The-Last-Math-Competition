/-!
# Conjecture 00000003831 is false (clause 1: symmetrized Schur nonnegativity)

Clause 1 of the conjecture: *for any finite crystal `B`, the coefficients of the Schur
expansion of the Weyl symmetrization of `ch(B)` are nonnegative.*

We formalize, from scratch (Lean 4 core only):

* `gl₃` crystals on a finite vertex type `Fin n`: weight map `wt : Fin n → ℤ³`, partial maps
  `e i, f i : Fin n → Option (Fin n)` and `ε i, φ i : Fin n → ℤ` for `i = 1, 2`
  (colour index `0 ↔ i = 1`, `1 ↔ i = 2`);
* Kashiwara's crystal axioms (`Crystal.IsCrystal`) and seminormality (`Crystal.IsSeminormal`,
  `ε_i(b) = max {k | e_iᵏ b ≠ 0}`, `φ_i(b) = max {k | f_iᵏ b ≠ 0}`, see `seminormal_eps_max`);
* Laurent polynomials in `x₁, x₂, x₃` (finite formal sums, equality = equality of all
  coefficients, `PolyEq`), multiplication, the `S₃`-action, the antisymmetrizer `J`, and
  the orbit sum;
* the character `ch B = Σ_b x^{wt b}`;
* Schur polynomials `schur λ` as generating functions of semistandard Young tableaux with
  entries in `{1,2,3}`; the bialternant formula `s_λ · a_ρ = a_{λ+ρ}` is checked;
* the Weyl symmetrization `π(f) = J(x^ρ f) / J(x^ρ)` through its defining equation
  `q · J(x^ρ) = J(x^ρ f)` (`WeylSym f q`).

The counterexample `B7` is a 7-vertex seminormal `gl₃` crystal (B(2,1,0) with one of its two
weight-(1,1,1) vertices removed and the strings re-glued).  `ch B7 = s₂₁₀ − s₁₁₁`, and every
reading of the symmetrization has a negative Schur coefficient.
-/

namespace Crystal3831

/-! ## Weights -/

/-- weights of `gl₃`: `ℤ³` -/
abbrev Wt := Int × Int × Int

def wadd (a b : Wt) : Wt := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
def wsub (a b : Wt) : Wt := (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)

theorem wadd_eq_iff (t e m : Wt) : wadd t e = m ↔ t = wsub m e := by
  obtain ⟨t1, t2, t3⟩ := t
  obtain ⟨e1, e2, e3⟩ := e
  obtain ⟨m1, m2, m3⟩ := m
  simp only [wadd, wsub, Prod.mk.injEq]
  omega

/-- simple roots `α₁ = ε₁ − ε₂` (index 0) and `α₂ = ε₂ − ε₃` (index 1) -/
def alpha (i : Fin 2) : Wt := if i.val = 0 then (1, -1, 0) else (0, 1, -1)

/-- the pairing `⟨h_i, w⟩` with the simple coroots -/
def pair (i : Fin 2) (w : Wt) : Int := if i.val = 0 then w.1 - w.2.1 else w.2.1 - w.2.2

/-- `ρ = (2,1,0)` -/
def rho : Wt := (2, 1, 0)

/-! ## Laurent polynomials in three variables -/

/-- a finite formal sum `Σ c · x^e` (an unnormalized list of terms) -/
abbrev Poly := List (Wt × Int)

/-- coefficient of `x^m` -/
def coeff : Poly → Wt → Int
  | [], _ => 0
  | (e, c) :: p, m => (if e = m then c else 0) + coeff p m

/-- equality of Laurent polynomials: all coefficients agree -/
def PolyEq (p q : Poly) : Prop := ∀ m, coeff p m = coeff q m

def smul (k : Int) (p : Poly) : Poly := p.map (fun t => (t.1, k * t.2))

/-- `x^e · c · p` -/
def shiftScale (p : Poly) (e : Wt) (c : Int) : Poly := p.map (fun t => (wadd t.1 e, t.2 * c))

/-- polynomial multiplication -/
def mul (p : Poly) : Poly → Poly
  | [] => []
  | (e, c) :: s => shiftScale p e c ++ mul p s

def mono (e : Wt) : Poly := [(e, 1)]

theorem coeff_append (p q : Poly) (m : Wt) : coeff (p ++ q) m = coeff p m + coeff q m := by
  induction p with
  | nil => simp [coeff]
  | cons t p ih =>
    obtain ⟨e, c⟩ := t
    simp only [List.cons_append, coeff, ih]
    omega

theorem coeff_smul (k : Int) (p : Poly) (m : Wt) : coeff (smul k p) m = k * coeff p m := by
  induction p with
  | nil => simp [smul, coeff]
  | cons t p ih =>
    obtain ⟨e, c⟩ := t
    have h : smul k ((e, c) :: p) = (e, k * c) :: smul k p := rfl
    rw [h, coeff, coeff, ih, Int.mul_add]
    by_cases he : e = m <;> simp [he]

theorem coeff_shiftScale (p : Poly) (e : Wt) (c : Int) (m : Wt) :
    coeff (shiftScale p e c) m = coeff p (wsub m e) * c := by
  induction p with
  | nil => simp [shiftScale, coeff]
  | cons t p ih =>
    obtain ⟨t1, t2⟩ := t
    have h : shiftScale ((t1, t2) :: p) e c = (wadd t1 e, t2 * c) :: shiftScale p e c := rfl
    rw [h, coeff, coeff, ih, Int.add_mul]
    by_cases he : t1 = wsub m e
    · have hw : wadd t1 e = m := (wadd_eq_iff _ _ _).mpr he
      rw [if_pos hw, if_pos he]
    · have : ¬ wadd t1 e = m := fun h' => he ((wadd_eq_iff _ _ _).mp h')
      simp [he, this]

theorem coeff_mul_congr (p p' s : Poly) (h : PolyEq p p') (m : Wt) :
    coeff (mul p s) m = coeff (mul p' s) m := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    obtain ⟨e, c⟩ := t
    simp only [mul, coeff_append, coeff_shiftScale, ih, h (wsub m e)]

theorem coeff_mul_append (p q s : Poly) (m : Wt) :
    coeff (mul (p ++ q) s) m = coeff (mul p s) m + coeff (mul q s) m := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    obtain ⟨e, c⟩ := t
    simp only [mul, coeff_append, coeff_shiftScale, ih, Int.add_mul]
    generalize coeff p (wsub m e) * c = A
    generalize coeff q (wsub m e) * c = B
    omega

theorem coeff_mul_smul (k : Int) (p s : Poly) (m : Wt) :
    coeff (mul (smul k p) s) m = k * coeff (mul p s) m := by
  induction s with
  | nil => simp [mul, coeff]
  | cons t s ih =>
    obtain ⟨e, c⟩ := t
    simp only [mul, coeff_append, coeff_shiftScale, coeff_smul, ih, Int.mul_add, Int.mul_assoc]

/-! ### Deciding polynomial equality (sound and complete) -/

theorem coeff_eq_zero (p : Poly) (m : Wt) (h : ∀ t ∈ p, t.1 ≠ m) : coeff p m = 0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    obtain ⟨e, c⟩ := t
    have h1 : e ≠ m := h (e, c) List.mem_cons_self
    have h2 : ∀ t ∈ p, t.1 ≠ m := fun t ht => h t (List.mem_cons_of_mem _ ht)
    simp [coeff, h1, ih h2]

def polyEqB (p q : Poly) : Bool := (p ++ q).all (fun t => coeff p t.1 == coeff q t.1)

theorem polyEqB_iff (p q : Poly) : polyEqB p q = true ↔ PolyEq p q := by
  constructor
  · intro h m
    have hall := List.all_eq_true.mp h
    by_cases hm : ∃ t ∈ p ++ q, t.1 = m
    · obtain ⟨t, ht, rfl⟩ := hm
      simpa using hall t ht
    · have hp : ∀ t ∈ p, t.1 ≠ m := fun t ht h' => hm ⟨t, List.mem_append_left _ ht, h'⟩
      have hq : ∀ t ∈ q, t.1 ≠ m := fun t ht h' => hm ⟨t, List.mem_append_right _ ht, h'⟩
      rw [coeff_eq_zero p m hp, coeff_eq_zero q m hq]
  · intro h
    apply List.all_eq_true.mpr
    intro t _
    simp [h t.1]

instance (p q : Poly) : Decidable (PolyEq p q) := decidable_of_iff _ (polyEqB_iff p q)

/-! ### The Weyl group `S₃`, the antisymmetrizer and the orbit sum -/

/-- the six permutations of the coordinates, with their signs -/
def perms : List ((Wt → Wt) × Int) :=
  [ (fun w => (w.1, w.2.1, w.2.2), 1),
    (fun w => (w.2.1, w.1, w.2.2), -1),
    (fun w => (w.1, w.2.2, w.2.1), -1),
    (fun w => (w.2.2, w.2.1, w.1), -1),
    (fun w => (w.2.1, w.2.2, w.1), 1),
    (fun w => (w.2.2, w.1, w.2.1), 1) ]

/-- `w · p` (permuting the variables) -/
def act (σ : Wt → Wt) (p : Poly) : Poly := p.map (fun t => (σ t.1, t.2))

/-- the antisymmetrizer `J(p) = Σ_w sgn(w) w(p)` -/
def J (p : Poly) : Poly := perms.flatMap (fun σ => smul σ.2 (act σ.1 p))

/-- the orbit sum `Σ_w w(p)` -/
def orb (p : Poly) : Poly := perms.flatMap (fun σ => act σ.1 p)

/-- `S₃`-invariance -/
def IsSymmetric (p : Poly) : Prop := ∀ σ ∈ perms, PolyEq (act σ.1 p) p

instance (p : Poly) : Decidable (IsSymmetric p) := by unfold IsSymmetric; infer_instance

/-- the Vandermonde `a_ρ = J(x^ρ)` -/
def aRho : Poly := J (mono rho)

/-- `q` is the Weyl symmetrization `J(x^ρ f)/J(x^ρ)` of `f`:  `q · J(x^ρ) = J(x^ρ · f)` -/
def WeylSym (f q : Poly) : Prop := PolyEq (mul q aRho) (J (mul (mono rho) f))

instance (f q : Poly) : Decidable (WeylSym f q) := by unfold WeylSym; infer_instance

/-- the Schur coefficient of `s_λ` in `π(f)` read off the bialternant expansion:
`[x^{λ+ρ}] J(x^ρ f)` -/
def schurCoeffW (f : Poly) (lam : Wt) : Int := coeff (J (mul (mono rho) f)) (wadd lam rho)

/-! ## Schur polynomials from semistandard Young tableaux -/

/-- all fillings of a row of length `l` with entries in `{1,2,3}` -/
def rowFill : Nat → List (List Nat)
  | 0 => [[]]
  | l + 1 => (rowFill l).flatMap (fun r => [1, 2, 3].map (fun a => a :: r))

/-- all fillings of a shape (list of row lengths) with entries in `{1,2,3}` -/
def fillings : List Nat → List (List (List Nat))
  | [] => [[]]
  | l :: sh => (fillings sh).flatMap (fun T => (rowFill l).map (fun r => r :: T))

def rowWeak : List Nat → Bool
  | a :: b :: r => decide (a ≤ b) && rowWeak (b :: r)
  | _ => true

/-- the columns between an upper row and the row below it increase strictly -/
def colStrict : List Nat → List Nat → Bool
  | a :: r, b :: r' => decide (a < b) && colStrict r r'
  | _, [] => true
  | [], _ :: _ => false

def isSSYT : List (List Nat) → Bool
  | [] => true
  | [r] => rowWeak r
  | r :: r' :: T => rowWeak r && colStrict r r' && isSSYT (r' :: T)

/-- the content `x^T` of a tableau -/
def content (T : List (List Nat)) : Wt :=
  ((T.flatten.count 1 : Nat), (T.flatten.count 2 : Nat), (T.flatten.count 3 : Nat))

/-- the Schur polynomial `s_λ(x₁,x₂,x₃) = Σ_{T ∈ SSYT(λ, 3)} x^T` -/
def schur (shape : List Nat) : Poly :=
  ((fillings shape).filter isSSYT).map (fun T => (content T, 1))

def s300 : Poly := schur [3]
def s210 : Poly := schur [2, 1]
def s111 : Poly := schur [1, 1, 1]
def s100 : Poly := schur [1]

theorem s300_card : s300.length = 10 := by decide +kernel
theorem s210_card : s210.length = 8 := by decide +kernel
theorem s111_eq : s111 = [((1, 1, 1), 1)] := by decide +kernel
theorem s100_eq : s100 = [((1, 0, 0), 1), ((0, 1, 0), 1), ((0, 0, 1), 1)] := by decide +kernel

/-- `s_210 = m_210 + 2 m_111` -/
theorem s210_monomials :
    PolyEq s210 [((2,1,0),1), ((1,2,0),1), ((2,0,1),1), ((0,2,1),1), ((1,0,2),1), ((0,1,2),1),
                 ((1,1,1),2)] := by decide +kernel

/-- the bialternant formula `s_λ · a_ρ = a_{λ+ρ}` for the three partitions of 3 -/
theorem bialternant_s300 : PolyEq (mul s300 aRho) (J (mono (5, 1, 0))) := by decide +kernel
theorem bialternant_s210 : PolyEq (mul s210 aRho) (J (mono (4, 2, 0))) := by decide +kernel
theorem bialternant_s111 : PolyEq (mul s111 aRho) (J (mono (3, 2, 1))) := by decide +kernel

theorem schur_symmetric : IsSymmetric s300 ∧ IsSymmetric s210 ∧ IsSymmetric s111 := by decide +kernel

/-- a degree-3 Schur expansion `a s₃₀₀ + b s₂₁₀ + c s₁₁₁` -/
def comb (a b c : Int) : Poly := smul a s300 ++ smul b s210 ++ smul c s111

/-- `q = a s₃₀₀ + b s₂₁₀ + c s₁₁₁` -/
def Expands (q : Poly) (a b c : Int) : Prop := PolyEq q (comb a b c)

instance (q : Poly) (a b c : Int) : Decidable (Expands q a b c) := by
  unfold Expands; infer_instance

theorem coeff_comb (a b c : Int) (m : Wt) :
    coeff (comb a b c) m = a * coeff s300 m + b * coeff s210 m + c * coeff s111 m := by
  simp only [comb, coeff_append, coeff_smul]

theorem coeff_mul_comb (a b c : Int) (s : Poly) (m : Wt) :
    coeff (mul (comb a b c) s) m =
      a * coeff (mul s300 s) m + b * coeff (mul s210 s) m + c * coeff (mul s111 s) m := by
  simp only [comb, coeff_mul_append, coeff_mul_smul]

/-- **Uniqueness of the Schur expansion** in degree 3: the Schur polynomials `s₃₀₀, s₂₁₀,
s₁₁₁` are linearly independent (unitriangular on `x³⁰⁰, x²¹⁰, x¹¹¹`). -/
theorem schur3_indep (a b c a' b' c' : Int) (h : PolyEq (comb a b c) (comb a' b' c')) :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := h (3, 0, 0)
  have h2 := h (2, 1, 0)
  have h3 := h (1, 1, 1)
  simp only [coeff_comb] at h1 h2 h3
  have e1 : coeff s300 (3, 0, 0) = 1 := by decide +kernel
  have e2 : coeff s210 (3, 0, 0) = 0 := by decide +kernel
  have e3 : coeff s111 (3, 0, 0) = 0 := by decide +kernel
  have e4 : coeff s300 (2, 1, 0) = 1 := by decide +kernel
  have e5 : coeff s210 (2, 1, 0) = 1 := by decide +kernel
  have e6 : coeff s111 (2, 1, 0) = 0 := by decide +kernel
  have e7 : coeff s300 (1, 1, 1) = 1 := by decide +kernel
  have e8 : coeff s210 (1, 1, 1) = 2 := by decide +kernel
  have e9 : coeff s111 (1, 1, 1) = 1 := by decide +kernel
  rw [e1, e2, e3] at h1
  rw [e4, e5, e6] at h2
  rw [e7, e8, e9] at h3
  omega

/-! ## Crystals -/

/-- a `gl₃` crystal datum on the finite vertex set `Fin n` -/
structure Crystal (n : Nat) where
  wt  : Fin n → Wt
  e   : Fin 2 → Fin n → Option (Fin n)
  f   : Fin 2 → Fin n → Option (Fin n)
  eps : Fin 2 → Fin n → Int
  phi : Fin 2 → Fin n → Int

variable {n : Nat}

/-- Kashiwara's axioms for a crystal (with integer-valued `ε, φ`) -/
def Crystal.IsCrystal (B : Crystal n) : Prop :=
  (∀ i b, B.phi i b = B.eps i b + pair i (B.wt b)) ∧
  (∀ i b b', B.f i b = some b' ↔ B.e i b' = some b) ∧
  (∀ i b b', B.e i b = some b' →
      B.wt b' = wadd (B.wt b) (alpha i) ∧ B.eps i b' = B.eps i b - 1 ∧ B.phi i b' = B.phi i b + 1) ∧
  (∀ i b b', B.f i b = some b' →
      B.wt b' = wsub (B.wt b) (alpha i) ∧ B.eps i b' = B.eps i b + 1 ∧ B.phi i b' = B.phi i b - 1)

/-- `g^k b` for a partial map `g` (`none` = the formal symbol `0`) -/
def iter (g : Fin n → Option (Fin n)) : Nat → Fin n → Option (Fin n)
  | 0, b => some b
  | k + 1, b => (iter g k b).bind g

/-- seminormality: `ε_i(b)` and `φ_i(b)` are the lengths of the `i`-string through `b` -/
def Crystal.IsSeminormal (B : Crystal n) : Prop :=
  ∀ i b, 0 ≤ B.eps i b ∧ (iter (B.e i) (B.eps i b).toNat b).isSome ∧
    iter (B.e i) ((B.eps i b).toNat + 1) b = none ∧
    0 ≤ B.phi i b ∧ (iter (B.f i) (B.phi i b).toNat b).isSome ∧
    iter (B.f i) ((B.phi i b).toNat + 1) b = none

instance (B : Crystal n) : Decidable B.IsCrystal := by unfold Crystal.IsCrystal; infer_instance
instance (B : Crystal n) : Decidable B.IsSeminormal := by
  unfold Crystal.IsSeminormal; infer_instance

theorem iter_none_succ (g : Fin n → Option (Fin n)) (k : Nat) (b : Fin n)
    (h : iter g k b = none) : iter g (k + 1) b = none := by
  simp [iter, h]

theorem iter_none_le (g : Fin n → Option (Fin n)) (k j : Nat) (b : Fin n)
    (h : iter g k b = none) (hkj : k ≤ j) : iter g j b = none := by
  induction j with
  | zero =>
    have : k = 0 := by omega
    subst this; exact h
  | succ j ih =>
    by_cases hk : k = j + 1
    · subst hk; exact h
    · exact iter_none_succ g j b (ih (by omega))

/-- seminormality means exactly `ε_i(b) = max {k | e_iᵏ b ≠ 0}` (and likewise for `φ`) -/
theorem seminormal_eps_max (B : Crystal n) (hB : B.IsSeminormal) (i : Fin 2) (b : Fin n)
    (k : Nat) : (iter (B.e i) k b).isSome ↔ k ≤ (B.eps i b).toNat := by
  obtain ⟨_, h1, h2, _⟩ := hB i b
  constructor
  · intro hk
    apply Classical.byContradiction
    intro hlt
    have := iter_none_le (B.e i) _ k b h2 (by omega)
    simp [this] at hk
  · intro hk
    apply Classical.byContradiction
    intro hns
    have hn : iter (B.e i) k b = none := by
      cases h : iter (B.e i) k b with
      | none => rfl
      | some _ => simp [h] at hns
    have := iter_none_le (B.e i) k _ b hn hk
    simp [this] at h1

theorem seminormal_phi_max (B : Crystal n) (hB : B.IsSeminormal) (i : Fin 2) (b : Fin n)
    (k : Nat) : (iter (B.f i) k b).isSome ↔ k ≤ (B.phi i b).toNat := by
  obtain ⟨_, _, _, _, h1, h2⟩ := hB i b
  constructor
  · intro hk
    apply Classical.byContradiction
    intro hlt
    have := iter_none_le (B.f i) _ k b h2 (by omega)
    simp [this] at hk
  · intro hk
    apply Classical.byContradiction
    intro hns
    have hn : iter (B.f i) k b = none := by
      cases h : iter (B.f i) k b with
      | none => rfl
      | some _ => simp [h] at hns
    have := iter_none_le (B.f i) k _ b hn hk
    simp [this] at h1

/-- the character `ch(B) = Σ_{b ∈ B} x^{wt b}` -/
def ch (B : Crystal n) : Poly := (List.finRange n).map (fun b => (B.wt b, 1))

/-- build a crystal on `Fin n` from tables indexed by vertex number -/
def mk (n : Nat) (wts : List Wt) (fs es : Fin 2 → List (Option (Fin n)))
    (epss phis : Fin 2 → List Int) : Crystal n where
  wt b := wts.getD b.val (0, 0, 0)
  f i b := (fs i).getD b.val none
  e i b := (es i).getD b.val none
  eps i b := (epss i).getD b.val 0
  phi i b := (phis i).getD b.val 0

/-! ## The counterexample: a 7-vertex seminormal `gl₃` crystal

Vertices `0..6 = A, B, C, D, E, F, Z` with weights
`A(2,1,0) B(1,2,0) C(2,0,1) D(0,2,1) E(1,0,2) F(0,1,2) Z(1,1,1)`.
`f₁ : A→B, C→Z→D, E→F`;  `f₂ : A→C, B→Z→E, D→F`. -/

def B7 : Crystal 7 :=
  mk 7 [(2,1,0), (1,2,0), (2,0,1), (0,2,1), (1,0,2), (0,1,2), (1,1,1)]
    -- f_i b       A        B        C        D        E        F        Z
    (fun i => if i.val = 0 then [some 1, none,   some 6, none,   some 5, none,   some 3]
                           else [some 2, some 6, none,   some 5, none,   none,   some 4])
    -- e_i b
    (fun i => if i.val = 0 then [none,   some 0, none,   some 6, none,   some 4, some 2]
                           else [none,   none,   some 0, none,   some 6, some 3, some 1])
    -- ε_i b          A  B  C  D  E  F  Z
    (fun i => if i.val = 0 then [0, 1, 0, 2, 0, 1, 1] else [0, 0, 1, 0, 2, 1, 1])
    -- φ_i b
    (fun i => if i.val = 0 then [1, 0, 2, 0, 1, 0, 1] else [1, 2, 0, 1, 0, 0, 1])

theorem B7_isCrystal : B7.IsCrystal := by decide +kernel
theorem B7_seminormal : B7.IsSeminormal := by decide +kernel

theorem ch_B7 : ch B7 = [((2,1,0),1), ((1,2,0),1), ((2,0,1),1), ((0,2,1),1), ((1,0,2),1),
    ((0,1,2),1), ((1,1,1),1)] := by decide +kernel

theorem ch_B7_symmetric : IsSymmetric (ch B7) := by decide +kernel

/-- `ch(B7) = s₂₁₀ − s₁₁₁` as polynomials -/
theorem ch_B7_expands : Expands (ch B7) 0 1 (-1) := by decide +kernel

/-- the Weyl symmetrizer fixes the symmetric polynomial `ch B7`: `ch · a_ρ = J(x^ρ ch)` -/
theorem weylSym_B7 : WeylSym (ch B7) (ch B7) := by decide +kernel

/-- `J(x^ρ ch B7) = a_{(4,2,0)} − a_{(3,2,1)}` -/
theorem J_B7 : PolyEq (J (mul (mono rho) (ch B7))) (J (mono (4,2,0)) ++ smul (-1) (J (mono (3,2,1)))) := by
  decide

/-- bialternant reading: the coefficients of `s₃₀₀, s₂₁₀, s₁₁₁` are `0, 1, −1` -/
theorem schurCoeffW_B7 :
    schurCoeffW (ch B7) (3,0,0) = 0 ∧ schurCoeffW (ch B7) (2,1,0) = 1 ∧
    schurCoeffW (ch B7) (1,1,1) = -1 := by decide +kernel

/-- **Robustness.** Whatever `q` satisfies the defining equation `q · J(x^ρ) = J(x^ρ ch B7)`
of the Weyl symmetrization, and whatever degree-3 Schur expansion `q = a s₃₀₀ + b s₂₁₀ + c s₁₁₁`
is chosen, necessarily `(a, b, c) = (0, 1, −1)`. -/
theorem weyl_forced (q : Poly) (hq : WeylSym (ch B7) q) (a b c : Int) (h : Expands q a b c) :
    a = 0 ∧ b = 1 ∧ c = -1 := by
  have key : ∀ m, coeff (J (mul (mono rho) (ch B7))) m =
      a * coeff (mul s300 aRho) m + b * coeff (mul s210 aRho) m + c * coeff (mul s111 aRho) m := by
    intro m
    rw [← hq m, coeff_mul_congr q (comb a b c) aRho h m, coeff_mul_comb]
  have h1 := key (5, 1, 0)
  have h2 := key (4, 2, 0)
  have h3 := key (3, 2, 1)
  have v1 : coeff (J (mul (mono rho) (ch B7))) (5, 1, 0) = 0 := by decide +kernel
  have v2 : coeff (J (mul (mono rho) (ch B7))) (4, 2, 0) = 1 := by decide +kernel
  have v3 : coeff (J (mul (mono rho) (ch B7))) (3, 2, 1) = -1 := by decide +kernel
  have e1 : coeff (mul s300 aRho) (5, 1, 0) = 1 := by decide +kernel
  have e2 : coeff (mul s210 aRho) (5, 1, 0) = 0 := by decide +kernel
  have e3 : coeff (mul s111 aRho) (5, 1, 0) = 0 := by decide +kernel
  have e4 : coeff (mul s300 aRho) (4, 2, 0) = 0 := by decide +kernel
  have e5 : coeff (mul s210 aRho) (4, 2, 0) = 1 := by decide +kernel
  have e6 : coeff (mul s111 aRho) (4, 2, 0) = 0 := by decide +kernel
  have e7 : coeff (mul s300 aRho) (3, 2, 1) = 0 := by decide +kernel
  have e8 : coeff (mul s210 aRho) (3, 2, 1) = 0 := by decide +kernel
  have e9 : coeff (mul s111 aRho) (3, 2, 1) = 1 := by decide +kernel
  rw [v1, e1, e2, e3] at h1
  rw [v2, e4, e5, e6] at h2
  rw [v3, e7, e8, e9] at h3
  omega

/-- orbit-sum reading: `Σ_w w(ch B7) = 6 s₂₁₀ − 6 s₁₁₁` -/
theorem orb_B7_expands : Expands (orb (ch B7)) 0 6 (-6) := by decide +kernel

theorem orbit_forced (a b c : Int) (h : Expands (orb (ch B7)) a b c) :
    a = 0 ∧ b = 6 ∧ c = -6 := by
  have h' : PolyEq (comb a b c) (comb 0 6 (-6)) := fun m => (h m).symm.trans (orb_B7_expands m)
  exact schur3_indep _ _ _ _ _ _ h'

/-- orbit-average reading `q = (1/6) Σ_w w(ch)`, stated integrally as `6 q = Σ_w w(ch)` -/
theorem avg_B7 : PolyEq (smul 6 (ch B7)) (orb (ch B7)) := by decide +kernel

theorem avg_forced (q : Poly) (hq : PolyEq (smul 6 q) (orb (ch B7))) (a b c : Int)
    (h : Expands q a b c) : a = 0 ∧ b = 1 ∧ c = -1 := by
  have h6 : PolyEq (comb (6 * a) (6 * b) (6 * c)) (comb 0 6 (-6)) := by
    intro m
    have := hq m
    rw [coeff_smul, h m, coeff_comb] at this
    rw [← orb_B7_expands m, ← this, coeff_comb]
    simp only [Int.mul_add, Int.mul_assoc]
  have := schur3_indep _ _ _ _ _ _ h6
  omega

/-! ## Non-vacuity: genuine normal crystals satisfy the same predicates -/

/-- `B(1,0,0)`: the standard crystal `1 →₁ 2 →₂ 3` -/
def B100 : Crystal 3 :=
  mk 3 [(1,0,0), (0,1,0), (0,0,1)]
    (fun i => if i.val = 0 then [some 1, none, none] else [none, some 2, none])
    (fun i => if i.val = 0 then [none, some 0, none] else [none, none, some 1])
    (fun i => if i.val = 0 then [0, 1, 0] else [0, 0, 1])
    (fun i => if i.val = 0 then [1, 0, 0] else [0, 1, 0])

theorem B100_ok : B100.IsCrystal ∧ B100.IsSeminormal ∧ PolyEq (ch B100) s100 ∧
    WeylSym (ch B100) s100 := by decide +kernel

/-- `B(2,1,0)` (tableaux `11/2, 12/2, 11/3, 12/3, 13/2, 13/3, 22/3, 23/3` = vertices 0..7);
`B7` is obtained from it by identifying the vertices `12/3` and `13/2`. -/
def B210 : Crystal 8 :=
  mk 8 [(2,1,0), (1,2,0), (2,0,1), (1,1,1), (1,1,1), (1,0,2), (0,2,1), (0,1,2)]
    (fun i => if i.val = 0 then [some 1, none, some 3, some 6, none, some 7, none, none]
                           else [some 2, some 4, none, none, some 5, none, some 7, none])
    (fun i => if i.val = 0 then [none, some 0, none, some 2, none, none, some 3, some 5]
                           else [none, none, some 0, none, some 1, some 4, none, some 6])
    (fun i => if i.val = 0 then [0, 1, 0, 1, 0, 0, 2, 1] else [0, 0, 1, 0, 1, 2, 0, 1])
    (fun i => if i.val = 0 then [1, 0, 2, 1, 0, 1, 0, 0] else [1, 2, 0, 0, 1, 0, 1, 0])

theorem B210_ok : B210.IsCrystal ∧ B210.IsSeminormal ∧ Expands (ch B210) 0 1 0 ∧
    WeylSym (ch B210) (ch B210) := by decide +kernel

/-- the axioms are not vacuous: a datum violating `φ − ε = ⟨h, wt⟩` is rejected -/
theorem broken_rejected : ¬ (mk 1 [(1,0,0)] (fun _ => [none]) (fun _ => [none])
    (fun _ => [0]) (fun _ => [0])).IsCrystal := by decide +kernel

/-- summary of the counterexample: `B7` is a seminormal crystal, its Weyl symmetrization is
`ch B7 = s₂₁₀ − s₁₁₁`, and in every Schur expansion of every Weyl symmetrization of `ch B7`
the coefficient of `s₁₁₁` is `−1 < 0`. -/
theorem B7_counterexample :
    B7.IsCrystal ∧ B7.IsSeminormal ∧ WeylSym (ch B7) (ch B7) ∧ Expands (ch B7) 0 1 (-1) ∧
    (∀ q, WeylSym (ch B7) q → ∀ a b c, Expands q a b c → c = -1) :=
  ⟨B7_isCrystal, B7_seminormal, weylSym_B7, ch_B7_expands,
    fun q hq a b c h => (weyl_forced q hq a b c h).2.2⟩

/-! ## The conjecture (clause 1) under each reading, and its refutation -/

/-- Clause 1, Weyl-symmetrizer reading `π(f) = J(x^ρ f)/J(x^ρ)`, restricted to seminormal
crystals (the restriction only weakens the claim). -/
def ClaimWeyl : Prop :=
  ∀ (n : Nat) (B : Crystal n), B.IsCrystal → B.IsSeminormal →
    ∀ q : Poly, WeylSym (ch B) q → ∀ a b c : Int, Expands q a b c → 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c

/-- Clause 1 for arbitrary (abstract Kashiwara) finite crystals, Weyl-symmetrizer reading -/
def ClaimWeylAbstract : Prop :=
  ∀ (n : Nat) (B : Crystal n), B.IsCrystal →
    ∀ q : Poly, WeylSym (ch B) q → ∀ a b c : Int, Expands q a b c → 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c

/-- Clause 1, bialternant form: the coefficient of `s_λ` in `π(f)` is `[x^{λ+ρ}] J(x^ρ f)` -/
def ClaimBialt : Prop :=
  ∀ (n : Nat) (B : Crystal n), B.IsCrystal → B.IsSeminormal →
    ∀ lam : Wt, lam.2.1 ≤ lam.1 → lam.2.2 ≤ lam.2.1 → 0 ≤ schurCoeffW (ch B) lam

/-- Clause 1, orbit-sum reading `Σ_w w(ch B)` -/
def ClaimOrbit : Prop :=
  ∀ (n : Nat) (B : Crystal n), B.IsCrystal → B.IsSeminormal →
    ∀ a b c : Int, Expands (orb (ch B)) a b c → 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c

/-- Clause 1, orbit-average reading `q = (1/6) Σ_w w(ch B)` -/
def ClaimAvg : Prop :=
  ∀ (n : Nat) (B : Crystal n), B.IsCrystal → B.IsSeminormal →
    ∀ q : Poly, PolyEq (smul 6 q) (orb (ch B)) →
      ∀ a b c : Int, Expands q a b c → 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c

theorem conjecture_00000003831_false : ¬ ClaimWeyl := by
  intro h
  have := h 7 B7 B7_isCrystal B7_seminormal (ch B7) weylSym_B7 0 1 (-1) ch_B7_expands
  omega

theorem conjecture_00000003831_false_abstract : ¬ ClaimWeylAbstract := by
  intro h
  have := h 7 B7 B7_isCrystal (ch B7) weylSym_B7 0 1 (-1) ch_B7_expands
  omega

theorem conjecture_00000003831_false_bialt : ¬ ClaimBialt := by
  intro h
  have := h 7 B7 B7_isCrystal B7_seminormal (1, 1, 1) (by decide +kernel) (by decide +kernel)
  rw [schurCoeffW_B7.2.2] at this
  omega

theorem conjecture_00000003831_false_orbit : ¬ ClaimOrbit := by
  intro h
  have := h 7 B7 B7_isCrystal B7_seminormal 0 6 (-6) orb_B7_expands
  omega

theorem conjecture_00000003831_false_avg : ¬ ClaimAvg := by
  intro h
  have := h 7 B7 B7_isCrystal B7_seminormal (ch B7) avg_B7 0 1 (-1) ch_B7_expands
  omega

end Crystal3831

#print axioms Crystal3831.conjecture_00000003831_false
#print axioms Crystal3831.conjecture_00000003831_false_abstract
#print axioms Crystal3831.conjecture_00000003831_false_bialt
#print axioms Crystal3831.conjecture_00000003831_false_orbit
#print axioms Crystal3831.conjecture_00000003831_false_avg
#print axioms Crystal3831.B7_counterexample
#print axioms Crystal3831.weyl_forced
#print axioms Crystal3831.orbit_forced
#print axioms Crystal3831.avg_forced
#print axioms Crystal3831.schur3_indep
#print axioms Crystal3831.seminormal_eps_max
#print axioms Crystal3831.B100_ok
#print axioms Crystal3831.B210_ok
