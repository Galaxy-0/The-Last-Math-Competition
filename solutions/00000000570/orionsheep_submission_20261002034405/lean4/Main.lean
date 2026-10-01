/-!
# Disproof of TLMC Conjecture 00000000570

Conjecture: for every acyclic cluster algebra, the width of the x-degree
support of the Laurent expansion (the Chebyshev-normalized invariant) is at
most 2·rank ("locality of degrees").

Counterexample: the Kronecker cluster algebra — rank 2, exchange matrix
B = [[0, 2], [-2, 0]] (affine type Ã₁, quiver 1 ⇉ 2, acyclic).  Its cluster
variables, expanded in the initial cluster (x₁, x₂), satisfy the recurrence

    xₙ₊₁ · xₙ₋₁ = xₙ² + 1          (n = 2, 3, 4, …)

with x₁ = x₁, x₂ = x₂.  The x₁-exponent of the support of xₙ spans the
interval [-(n-2), n-4], i.e. the support width is 2(n-3): 0, 2, 4, 6, 8, 10,
12, … for n = 3, 4, 5, 6, 7, 8, 9, … — unbounded, hence > 2·rank = 4 from
x₆ on.

Formalized facts (core Lean only, no Mathlib, zero axioms, zero `sorry`):

* Tables `TBL1 … TBL9` list the Laurent expansions of x₁ … x₉ about (x₁, x₂),
  as computed by `reproduce.py` (greedy exact division, remultiplied).
* `coeffOf t k` is the coefficient of x₁^{k.1} x₂^{k.2} in the Laurent
  polynomial given by term list `t`; `prodCoef p q k` is the coefficient of
  the Cauchy product; `plus1 k` is the coefficient of the constant 1.
* `relz2 … relz8` — all seven exchange relations hold coefficientwise:
  xₙ₋₁ · xₙ₊₁ = xₙ² + 1 for n = 2 … 8, pinning the tables down as the
  Laurent expansions of the cluster variables (uniqueness in the Laurent
  polynomial ring follows from cancellation in the domain ℤ[x₁^±1, x₂^±1]).
* `width3 … width9` — the support of xₙ lies in the x₁-strip
  [-(n-2), n-4], and both endpoint exponents are attained with nonzero
  coefficient, so the widths are exactly 0, 2, 4, 6, 8, 10, 12.
* `disproof_00000000570` — packages the chain and the violations at x₆
  (width 6 > 2·2 = 4) and x₉ (width 12 > 4).

Style: `decide` only on closed propositions; `omega`, `simp` and
`native_decide` are avoided entirely (the first two can pull in
`propext`/`Quot.sound`); all open-goal reasoning is term-mode `Eq`/
`congrArg` composition and case analysis.  `Check.lean` audits
`#print axioms` for every declaration.
-/

/-! ## Laurent polynomial bookkeeping -/

/-- Exponent key `(a, b)` standing for x₁^a x₂^b. -/
abbrev Key := Int × Int

/-- Term `(key, c)`: the monomial x₁^{key.1} x₂^{key.2} with coefficient c. -/
abbrev Ent := Key × Int

/-- A Laurent polynomial in x₁, x₂ given by a term list (with multiplicity). -/
abbrev T := List Ent

/-- Coefficient of x₁^{k.1} x₂^{k.2} in the polynomial given by term list t
(sum over entries whose key equals k). -/
def coeffOf : T → Key → Int
  | [], _ => 0
  | m :: t, k => if m.1 = k then m.2 + coeffOf t k else coeffOf t k

/-- Contribution of one term m ∈ p to the coefficient of exponent k in the
product p·q: sum the pairwise coefficient products whose exponents add to k. -/
def termCoef : Ent → T → Key → Int
  | _, [], _ => 0
  | m, n :: q, k =>
      if m.1.1 + n.1.1 = k.1 ∧ m.1.2 + n.1.2 = k.2 then m.2 * n.2
      else termCoef m q k

/-- Coefficient of exponent k in the product of the polynomials p and q
(Cauchy product formula, term by term). -/
def prodCoef : T → T → Key → Int
  | [], _, _ => 0
  | m :: p, q, k => termCoef m q k + prodCoef p q k

/-- Coefficient function of the constant Laurent polynomial 1. -/
def plus1 (k : Key) : Int := if k = (0, 0) then 1 else 0

theorem coeffOf_cons (m : Ent) (t : T) (k : Key) :
    coeffOf (m :: t) k = (if m.1 = k then m.2 + coeffOf t k else coeffOf t k) :=
  rfl

theorem termCoef_cons (m : Ent) (n : Ent) (q : T) (k : Key) :
    termCoef m (n :: q) k =
      (if m.1.1 + n.1.1 = k.1 ∧ m.1.2 + n.1.2 = k.2 then m.2 * n.2
       else termCoef m q k) :=
  rfl

theorem prodCoef_cons (m : Ent) (p q : T) (k : Key) :
    prodCoef (m :: p) q k = termCoef m q k + prodCoef p q k :=
  rfl

/-- Case analysis for list membership. -/
theorem memcase {α : Type} {a y : α} {l : List α} (h : List.Mem a (y :: l)) :
    a = y ∨ List.Mem a l := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h' => exact Or.inr h'

/-! ## Decidable finite quantifiers (axiom-free, kernel-evaluated) -/

/-- Finite quantifier over a literal list, membership-as-`∈` form. -/
def decForallMem {α : Type} (p : α → Prop) (d : (a : α) → Decidable (p a)) :
    (l : List α) → Decidable (∀ x ∈ l, p x)
  | [] => isTrue (fun _x hx => nomatch hx)
  | a :: l =>
    match d a with
    | isTrue ha =>
      match decForallMem p d l with
      | isTrue hl => isTrue (fun x hx => match memcase hx with
          | Or.inl he => he ▸ ha
          | Or.inr hm => hl x hm)
      | isFalse hl =>
        isFalse (fun hcon => hl (fun y hy => hcon y (List.Mem.tail _ hy)))
    | isFalse ha => isFalse (fun hcon => absurd (hcon a (List.Mem.head _)) ha)

/-- Finite quantifier over a literal list, `List.Mem` form. -/
def decForallMemL {α : Type} (p : α → Prop) (d : (a : α) → Decidable (p a)) :
    (l : List α) → Decidable (∀ x, List.Mem x l → p x)
  | [] => isTrue (fun _x hx => nomatch hx)
  | a :: l =>
    match d a with
    | isTrue ha =>
      match decForallMemL p d l with
      | isTrue hl => isTrue (fun x hx => match memcase hx with
          | Or.inl he => he ▸ ha
          | Or.inr hm => hl x hm)
      | isFalse hl =>
        isFalse (fun hcon => hl (fun x hx => hcon x (List.Mem.tail _ hx)))
    | isFalse ha => isFalse (fun hcon => absurd (hcon a (List.Mem.head _)) ha)

instance instDFM {α : Type} {p : α → Prop} [d : (a : α) → Decidable (p a)]
    (l : List α) : Decidable (∀ x ∈ l, p x) := decForallMem p d l

instance instDFML {α : Type} {p : α → Prop} [d : (a : α) → Decidable (p a)]
    (l : List α) : Decidable (∀ x, List.Mem x l → p x) := decForallMemL p d l

/-! ## The generic package: exchange relation + width from decidable facts -/

theorem coeffOf_ne_mem : ∀ (t : T) (k : Key), coeffOf t k ≠ 0 →
    ∃ m, List.Mem m t ∧ m.1 = k := by
  intro t
  induction t with
  | nil => intro k h; exact absurd rfl h
  | cons m t ih =>
    intro k h
    rw [coeffOf_cons] at h
    refine Decidable.byCases (p := m.1 = k) ?_ ?_
    · intro he
      exact ⟨m, List.Mem.head _, he⟩
    · intro he
      rw [if_neg he] at h
      cases ih k h with
      | intro n hn => exact ⟨n, List.Mem.tail _ hn.1, hn.2⟩

/-- A nonzero product coefficient forces a contributing pair to exist. -/
theorem termCoef_ne : ∀ (m : Ent) (q : T) (k : Key), termCoef m q k ≠ 0 →
    ∃ n, List.Mem n q ∧ m.1.1 + n.1.1 = k.1 ∧ m.1.2 + n.1.2 = k.2 := by
  intro m q
  induction q with
  | nil => intro k h; exact absurd rfl h
  | cons n q ih =>
    intro k h
    rw [termCoef_cons] at h
    refine Decidable.byCases
      (p := m.1.1 + n.1.1 = k.1 ∧ m.1.2 + n.1.2 = k.2) ?_ ?_
    · intro hc
      exact ⟨n, List.Mem.head _, hc.1, hc.2⟩
    · intro hc
      rw [if_neg hc] at h
      cases ih k h with
      | intro n' hn => exact ⟨n', List.Mem.tail _ hn.1, hn.2.1, hn.2.2⟩

/-- A nonzero product coefficient forces an exponent-summing pair to exist. -/
theorem prodCoef_ne : ∀ (p q : T) (k : Key), prodCoef p q k ≠ 0 →
    ∃ m, List.Mem m p ∧ ∃ n, List.Mem n q ∧
      m.1.1 + n.1.1 = k.1 ∧ m.1.2 + n.1.2 = k.2 := by
  intro p
  induction p with
  | nil => intro q k h; exact absurd rfl h
  | cons m p ih =>
    intro q k h
    rw [prodCoef_cons] at h
    refine Decidable.byCases (p := termCoef m q k = 0) ?_ ?_
    · intro hz
      have h' : prodCoef p q k ≠ 0 := by
        intro h0
        apply h
        rw [hz, h0]
        rfl
      cases ih q k h' with
      | intro m' hm' => exact ⟨m', List.Mem.tail _ hm'.1, hm'.2⟩
    · intro hnz
      cases termCoef_ne m q k hnz with
      | intro n hn =>
        exact ⟨m, List.Mem.head _, n, hn.1, hn.2.1, hn.2.2⟩

/-- Pair equality out of component equalities. -/
theorem eq_pair {a b c d : Int} (h1 : a = c) (h2 : b = d) : (a, b) = (c, d) := by
  cases h1
  cases h2
  rfl

/-- Membership transports along an equality of keys. -/
theorem mem_of_pair_eq {KEYS : List Key} {p k : Key} (h : p = k)
    (hm : List.Mem p KEYS) : List.Mem k KEYS := by
  cases h
  exact hm


/-- Indicator table of a key list: coefficient 1 at each key. -/
def indOf : List Key → T
  | [] => []
  | k :: l => (k, 1) :: indOf l

/-- Every key of `indOf l` is a member of `l` (structural induction). -/
theorem keysind_supp_gen : ∀ (l : List Key) (m : Ent),
    List.Mem m (indOf l) → List.Mem m.1 l := by
  intro l
  induction l with
  | nil => intro m hm; cases hm
  | cons k l ih =>
    intro m hm
    cases hm with
    | head => exact List.Mem.head l
    | tail _ h' => exact List.Mem.tail k (ih m h')

/-- A nonzero coefficient in the indicator table means membership. -/
theorem mem_of_keysind (KEYS : List Key) (k : Key)
    (hc : coeffOf (indOf KEYS) k ≠ 0) : List.Mem k KEYS := by
  cases coeffOf_ne_mem (indOf KEYS) k hc with
  | intro m hm => rw [← hm.2]; exact keysind_supp_gen KEYS m hm.1


/-! ## The generic package: exchange relation + width from decidable facts -/

/--
One-size relation assembler (coefficient-indicator form): if `KEYSind` is a
Laurent polynomial whose support is exactly the common key set (all
coefficients 1), the two sides agree coefficientwise at every key of that
support, the support contains the pairwise sums of P·Q and of R·R (all
coefficients nonzero there), and contains (0, 0), then the two sides agree
coefficientwise everywhere.  Uses no decidability of `List.Mem` (only
`Int` arithmetic), so every `decide` reduces in the kernel. -/
theorem rel_of_keys (P Q R : T) (KEYSind : T)
    (hkeys : ∀ k, coeffOf KEYSind k ≠ 0 → prodCoef P Q k = prodCoef R R k + plus1 k)
    (hsuppPQ : ∀ m, List.Mem m P → ∀ n, List.Mem n Q →
      coeffOf KEYSind (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0)
    (hsuppRR : ∀ m, List.Mem m R → ∀ n, List.Mem n R →
      coeffOf KEYSind (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0)
    (hzero : coeffOf KEYSind (0, 0) ≠ 0) :
    ∀ k, prodCoef P Q k = prodCoef R R k + plus1 k := by
  intro k
  refine Decidable.byCases (p := coeffOf KEYSind k ≠ 0) (fun hk => hkeys k hk) ?_
  intro hk
  have hPQ : prodCoef P Q k = 0 := by
    refine Decidable.byCases (p := prodCoef P Q k = 0) ?_ ?_
    · intro hzz; exact hzz
    · intro hnz
      cases prodCoef_ne P Q k hnz with
      | intro m hm =>
        cases hm.2 with
        | intro n hn =>
          have h1 := hsuppPQ m hm.1 n hn.1
          rw [eq_pair hn.2.1 hn.2.2] at h1
          exact absurd h1 hk
  have hRR : prodCoef R R k = 0 := by
    refine Decidable.byCases (p := prodCoef R R k = 0) ?_ ?_
    · intro hzz; exact hzz
    · intro hnz
      cases prodCoef_ne R R k hnz with
      | intro m hm =>
        cases hm.2 with
        | intro n hn =>
          have h1 := hsuppRR m hm.1 n hn.1
          rw [eq_pair hn.2.1 hn.2.2] at h1
          exact absurd h1 hk
  have h01 : plus1 k = 0 := by
    refine Decidable.byCases (p := k = (0, 0)) ?_ ?_
    · intro he
      rw [he] at hk
      exact absurd hzero hk
    · intro he
      show (if k = (0, 0) then (1 : Int) else 0) = 0
      exact if_neg he
  rw [hPQ, hRR, h01]
  rfl

/-- Width bound from a decidable per-term strip condition. -/
theorem width_bound_aux : ∀ (t : T) (lo hi : Int),
    (∀ m, List.Mem m t → lo ≤ m.1.1 ∧ m.1.1 ≤ hi) →
    ∀ k, coeffOf t k ≠ 0 → lo ≤ k.1 ∧ k.1 ≤ hi := by
  intro t
  induction t with
  | nil => intro _ _ _ k h; exact absurd rfl h
  | cons m t ih =>
    intro lo hi hkeys k h
    rw [coeffOf_cons] at h
    refine Decidable.byCases (p := m.1 = k) ?_ ?_
    · intro he
      have h1 : m.1.1 = k.1 := congrArg (fun t : Key => t.1) he
      have hb := hkeys m (List.Mem.head _)
      exact ⟨h1 ▸ hb.1, h1 ▸ hb.2⟩
    · intro he
      rw [if_neg he] at h
      exact ih lo hi (fun x hx => hkeys x (List.Mem.tail _ hx)) k h

/-! ## The Kronecker expansions x₁ … x₉ (from reproduce.py) -/

def TBL1 : T := [
  ((1, 0), 1)
]
def TBL2 : T := [
  ((0, 1), 1)
]
def TBL3 : T := [
  ((-1, 0), 1), ((-1, 2), 1)
]
def TBL4 : T := [
  ((-2, -1), 1), ((-2, 1), 2), ((-2, 3), 1), ((0, -1), 1)
]
def TBL5 : T := [
  ((-3, -2), 1), ((-3, 0), 3), ((-3, 2), 3), ((-3, 4), 1),
  ((-1, -2), 2), ((-1, 0), 2), ((1, -2), 1)
]
def TBL6 : T := [
  ((-4, -3), 1), ((-4, -1), 4), ((-4, 1), 6), ((-4, 3), 4),
  ((-4, 5), 1), ((-2, -3), 3), ((-2, -1), 6), ((-2, 1), 3),
  ((0, -3), 3), ((0, -1), 2), ((2, -3), 1)
]
def TBL7 : T := [
  ((-5, -4), 1), ((-5, -2), 5), ((-5, 0), 10), ((-5, 2), 10),
  ((-5, 4), 5), ((-5, 6), 1), ((-3, -4), 4), ((-3, -2), 12),
  ((-3, 0), 12), ((-3, 2), 4), ((-1, -4), 6), ((-1, -2), 9),
  ((-1, 0), 3), ((1, -4), 4), ((1, -2), 2), ((3, -4), 1)
]
def TBL8 : T := [
  ((-6, -5), 1), ((-6, -3), 6), ((-6, -1), 15), ((-6, 1), 20),
  ((-6, 3), 15), ((-6, 5), 6), ((-6, 7), 1), ((-4, -5), 5),
  ((-4, -3), 20), ((-4, -1), 30), ((-4, 1), 20), ((-4, 3), 5),
  ((-2, -5), 10), ((-2, -3), 24), ((-2, -1), 18), ((-2, 1), 4),
  ((0, -5), 10), ((0, -3), 12), ((0, -1), 3), ((2, -5), 5),
  ((2, -3), 2), ((4, -5), 1)
]
def TBL9 : T := [
  ((-7, -6), 1), ((-7, -4), 7), ((-7, -2), 21), ((-7, 0), 35),
  ((-7, 2), 35), ((-7, 4), 21), ((-7, 6), 7), ((-7, 8), 1),
  ((-5, -6), 6), ((-5, -4), 30), ((-5, -2), 60), ((-5, 0), 60),
  ((-5, 2), 30), ((-5, 4), 6), ((-3, -6), 15), ((-3, -4), 50),
  ((-3, -2), 60), ((-3, 0), 30), ((-3, 2), 5), ((-1, -6), 20),
  ((-1, -4), 40), ((-1, -2), 24), ((-1, 0), 4), ((1, -6), 15),
  ((1, -4), 15), ((1, -2), 3), ((3, -6), 6), ((3, -4), 2),
  ((5, -6), 1)
]
def KEYS2 : List Key := [
  (0, 0), (0, 2)
]
def KEYS3 : List Key := [
  (-2, 0), (-2, 2), (-2, 4), (0, 0)
]
def KEYS4 : List Key := [
  (-4, -2), (-4, 0), (-4, 2), (-4, 4), (-4, 6), (-2, -2), (-2, 0),
  (-2, 2), (0, -2), (0, 0)
]
def KEYS5 : List Key := [
  (-6, -4), (-6, -2), (-6, 0), (-6, 2), (-6, 4), (-6, 6), (-6, 8),
  (-4, -4), (-4, -2), (-4, 0), (-4, 2), (-4, 4), (-2, -4), (-2, -2),
  (-2, 0), (-2, 2), (0, -4), (0, -2), (0, 0), (2, -4)
]
def KEYS6 : List Key := [
  (-8, -6), (-8, -4), (-8, -2), (-8, 0), (-8, 2), (-8, 4), (-8, 6),
  (-8, 8), (-8, 10), (-6, -6), (-6, -4), (-6, -2), (-6, 0), (-6, 2),
  (-6, 4), (-6, 6), (-4, -6), (-4, -4), (-4, -2), (-4, 0), (-4, 2),
  (-4, 4), (-2, -6), (-2, -4), (-2, -2), (-2, 0), (-2, 2), (0, -6),
  (0, -4), (0, -2), (0, 0), (2, -6), (2, -4), (4, -6)
]
def KEYS7 : List Key := [
  (-10, -8), (-10, -6), (-10, -4), (-10, -2), (-10, 0), (-10, 2),
  (-10, 4), (-10, 6), (-10, 8), (-10, 10), (-10, 12), (-8, -8),
  (-8, -6), (-8, -4), (-8, -2), (-8, 0), (-8, 2), (-8, 4), (-8, 6),
  (-8, 8), (-6, -8), (-6, -6), (-6, -4), (-6, -2), (-6, 0), (-6, 2),
  (-6, 4), (-6, 6), (-4, -8), (-4, -6), (-4, -4), (-4, -2), (-4, 0),
  (-4, 2), (-4, 4), (-2, -8), (-2, -6), (-2, -4), (-2, -2), (-2, 0),
  (-2, 2), (0, -8), (0, -6), (0, -4), (0, -2), (0, 0), (2, -8),
  (2, -6), (2, -4), (4, -8), (4, -6), (6, -8)
]
def KEYS8 : List Key := [
  (-12, -10), (-12, -8), (-12, -6), (-12, -4), (-12, -2), (-12, 0),
  (-12, 2), (-12, 4), (-12, 6), (-12, 8), (-12, 10), (-12, 12),
  (-12, 14), (-10, -10), (-10, -8), (-10, -6), (-10, -4), (-10, -2),
  (-10, 0), (-10, 2), (-10, 4), (-10, 6), (-10, 8), (-10, 10),
  (-8, -10), (-8, -8), (-8, -6), (-8, -4), (-8, -2), (-8, 0), (-8, 2),
  (-8, 4), (-8, 6), (-8, 8), (-6, -10), (-6, -8), (-6, -6), (-6, -4),
  (-6, -2), (-6, 0), (-6, 2), (-6, 4), (-6, 6), (-4, -10), (-4, -8),
  (-4, -6), (-4, -4), (-4, -2), (-4, 0), (-4, 2), (-4, 4), (-2, -10),
  (-2, -8), (-2, -6), (-2, -4), (-2, -2), (-2, 0), (-2, 2), (0, -10),
  (0, -8), (0, -6), (0, -4), (0, -2), (0, 0), (2, -10), (2, -8),
  (2, -6), (2, -4), (4, -10), (4, -8), (4, -6), (6, -10), (6, -8),
  (8, -10)
]


/-! ## The seven exchange relations xₙ₋₁ · xₙ₊₁ = xₙ² + 1 -/




theorem relz2 : ∀ k, prodCoef TBL1 TBL3 k = prodCoef TBL2 TBL2 k + plus1 k := by
  have hkeys : ∀ k ∈ KEYS2, coeffOf (indOf KEYS2) k ≠ 0 →
      prodCoef TBL1 TBL3 k = prodCoef TBL2 TBL2 k + plus1 k :=
    of_decide_eq_true (by decide)
  have hsuppPQ : ∀ m ∈ TBL1, ∀ n ∈ TBL3,
      coeffOf (indOf KEYS2) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hsuppRR : ∀ m ∈ TBL2, ∀ n ∈ TBL2,
      coeffOf (indOf KEYS2) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hzero : coeffOf (indOf KEYS2) (0, 0) ≠ 0 := of_decide_eq_true (by decide)
  intro k
  exact rel_of_keys TBL1 TBL3 TBL2 (indOf KEYS2)
    (fun j hk => hkeys j (mem_of_keysind KEYS2 j hk) hk) hsuppPQ hsuppRR hzero k

theorem relz3 : ∀ k, prodCoef TBL2 TBL4 k = prodCoef TBL3 TBL3 k + plus1 k := by
  have hkeys : ∀ k ∈ KEYS3, coeffOf (indOf KEYS3) k ≠ 0 →
      prodCoef TBL2 TBL4 k = prodCoef TBL3 TBL3 k + plus1 k :=
    of_decide_eq_true (by decide)
  have hsuppPQ : ∀ m ∈ TBL2, ∀ n ∈ TBL4,
      coeffOf (indOf KEYS3) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hsuppRR : ∀ m ∈ TBL3, ∀ n ∈ TBL3,
      coeffOf (indOf KEYS3) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hzero : coeffOf (indOf KEYS3) (0, 0) ≠ 0 := of_decide_eq_true (by decide)
  intro k
  exact rel_of_keys TBL2 TBL4 TBL3 (indOf KEYS3)
    (fun j hk => hkeys j (mem_of_keysind KEYS3 j hk) hk) hsuppPQ hsuppRR hzero k

theorem relz4 : ∀ k, prodCoef TBL3 TBL5 k = prodCoef TBL4 TBL4 k + plus1 k := by
  have hkeys : ∀ k ∈ KEYS4, coeffOf (indOf KEYS4) k ≠ 0 →
      prodCoef TBL3 TBL5 k = prodCoef TBL4 TBL4 k + plus1 k :=
    of_decide_eq_true (by decide)
  have hsuppPQ : ∀ m ∈ TBL3, ∀ n ∈ TBL5,
      coeffOf (indOf KEYS4) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hsuppRR : ∀ m ∈ TBL4, ∀ n ∈ TBL4,
      coeffOf (indOf KEYS4) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hzero : coeffOf (indOf KEYS4) (0, 0) ≠ 0 := of_decide_eq_true (by decide)
  intro k
  exact rel_of_keys TBL3 TBL5 TBL4 (indOf KEYS4)
    (fun j hk => hkeys j (mem_of_keysind KEYS4 j hk) hk) hsuppPQ hsuppRR hzero k

theorem relz5 : ∀ k, prodCoef TBL4 TBL6 k = prodCoef TBL5 TBL5 k + plus1 k := by
  have hkeys : ∀ k ∈ KEYS5, coeffOf (indOf KEYS5) k ≠ 0 →
      prodCoef TBL4 TBL6 k = prodCoef TBL5 TBL5 k + plus1 k :=
    of_decide_eq_true (by decide)
  have hsuppPQ : ∀ m ∈ TBL4, ∀ n ∈ TBL6,
      coeffOf (indOf KEYS5) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hsuppRR : ∀ m ∈ TBL5, ∀ n ∈ TBL5,
      coeffOf (indOf KEYS5) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hzero : coeffOf (indOf KEYS5) (0, 0) ≠ 0 := of_decide_eq_true (by decide)
  intro k
  exact rel_of_keys TBL4 TBL6 TBL5 (indOf KEYS5)
    (fun j hk => hkeys j (mem_of_keysind KEYS5 j hk) hk) hsuppPQ hsuppRR hzero k

theorem relz6 : ∀ k, prodCoef TBL5 TBL7 k = prodCoef TBL6 TBL6 k + plus1 k := by
  have hkeys : ∀ k ∈ KEYS6, coeffOf (indOf KEYS6) k ≠ 0 →
      prodCoef TBL5 TBL7 k = prodCoef TBL6 TBL6 k + plus1 k :=
    of_decide_eq_true (by decide)
  have hsuppPQ : ∀ m ∈ TBL5, ∀ n ∈ TBL7,
      coeffOf (indOf KEYS6) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hsuppRR : ∀ m ∈ TBL6, ∀ n ∈ TBL6,
      coeffOf (indOf KEYS6) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hzero : coeffOf (indOf KEYS6) (0, 0) ≠ 0 := of_decide_eq_true (by decide)
  intro k
  exact rel_of_keys TBL5 TBL7 TBL6 (indOf KEYS6)
    (fun j hk => hkeys j (mem_of_keysind KEYS6 j hk) hk) hsuppPQ hsuppRR hzero k

theorem relz7 : ∀ k, prodCoef TBL6 TBL8 k = prodCoef TBL7 TBL7 k + plus1 k := by
  have hkeys : ∀ k ∈ KEYS7, coeffOf (indOf KEYS7) k ≠ 0 →
      prodCoef TBL6 TBL8 k = prodCoef TBL7 TBL7 k + plus1 k :=
    of_decide_eq_true (by decide)
  have hsuppPQ : ∀ m ∈ TBL6, ∀ n ∈ TBL8,
      coeffOf (indOf KEYS7) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hsuppRR : ∀ m ∈ TBL7, ∀ n ∈ TBL7,
      coeffOf (indOf KEYS7) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hzero : coeffOf (indOf KEYS7) (0, 0) ≠ 0 := of_decide_eq_true (by decide)
  intro k
  exact rel_of_keys TBL6 TBL8 TBL7 (indOf KEYS7)
    (fun j hk => hkeys j (mem_of_keysind KEYS7 j hk) hk) hsuppPQ hsuppRR hzero k

set_option maxHeartbeats 1000000 in
theorem relz8 : ∀ k, prodCoef TBL7 TBL9 k = prodCoef TBL8 TBL8 k + plus1 k := by
  have hkeys : ∀ k ∈ KEYS8, coeffOf (indOf KEYS8) k ≠ 0 →
      prodCoef TBL7 TBL9 k = prodCoef TBL8 TBL8 k + plus1 k :=
    of_decide_eq_true (by decide)
  have hsuppPQ : ∀ m ∈ TBL7, ∀ n ∈ TBL9,
      coeffOf (indOf KEYS8) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hsuppRR : ∀ m ∈ TBL8, ∀ n ∈ TBL8,
      coeffOf (indOf KEYS8) (m.1.1 + n.1.1, m.1.2 + n.1.2) ≠ 0 :=
    of_decide_eq_true (by decide)
  have hzero : coeffOf (indOf KEYS8) (0, 0) ≠ 0 := of_decide_eq_true (by decide)
  intro k
  exact rel_of_keys TBL7 TBL9 TBL8 (indOf KEYS8)
    (fun j hk => hkeys j (mem_of_keysind KEYS8 j hk) hk) hsuppPQ hsuppRR hzero k
/-! ## Support widths of x₃ … x₉: exactly 0, 2, 4, 6, 8, 10, 12 -/

theorem width3 : ∀ k, coeffOf TBL3 k ≠ 0 → (-1 : Int) ≤ k.1 ∧ k.1 ≤ -1 :=
  width_bound_aux TBL3 (-1) (-1) (of_decide_eq_true (by decide))

theorem width4 : ∀ k, coeffOf TBL4 k ≠ 0 → (-2 : Int) ≤ k.1 ∧ k.1 ≤ 0 :=
  width_bound_aux TBL4 (-2) 0 (of_decide_eq_true (by decide))

theorem width5 : ∀ k, coeffOf TBL5 k ≠ 0 → (-3 : Int) ≤ k.1 ∧ k.1 ≤ 1 :=
  width_bound_aux TBL5 (-3) 1 (of_decide_eq_true (by decide))

theorem width6 : ∀ k, coeffOf TBL6 k ≠ 0 → (-4 : Int) ≤ k.1 ∧ k.1 ≤ 2 :=
  width_bound_aux TBL6 (-4) 2 (of_decide_eq_true (by decide))

theorem width7 : ∀ k, coeffOf TBL7 k ≠ 0 → (-5 : Int) ≤ k.1 ∧ k.1 ≤ 3 :=
  width_bound_aux TBL7 (-5) 3 (of_decide_eq_true (by decide))

theorem width8 : ∀ k, coeffOf TBL8 k ≠ 0 → (-6 : Int) ≤ k.1 ∧ k.1 ≤ 4 :=
  width_bound_aux TBL8 (-6) 4 (of_decide_eq_true (by decide))

theorem width9 : ∀ k, coeffOf TBL9 k ≠ 0 → (-7 : Int) ≤ k.1 ∧ k.1 ≤ 5 :=
  width_bound_aux TBL9 (-7) 5 (of_decide_eq_true (by decide))

/-- Both strip endpoints of x₆ are attained (nonzero coefficients). -/
example : coeffOf TBL6 (-4, -3) ≠ 0 ∧ coeffOf TBL6 (2, -3) ≠ 0 := by decide

/-- Both strip endpoints of x₉ are attained. -/
example : coeffOf TBL9 (-7, -6) ≠ 0 ∧ coeffOf TBL9 (5, -6) ≠ 0 := by decide

/-- Widths 0, 2, 4, 6, 8, 10, 12 for x₃ … x₉. -/
example : ((-1) - (-1) : Int) = 0 := rfl
example : (0 - (-2) : Int) = 2 := rfl
example : (1 - (-3) : Int) = 4 := rfl
example : (2 - (-4) : Int) = 6 := rfl
example : (3 - (-5) : Int) = 8 := rfl
example : (4 - (-6) : Int) = 10 := rfl
example : (5 - (-7) : Int) = 12 := rfl

/-! ## The disproof -/

/-- Main disproof of conjecture 00000000570.

The Kronecker cluster algebra (rank 2, acyclic, affine Ã₁) violates the
claimed bound 2·rank = 4 on the x-degree support width of Laurent
expansions: the cluster variable x₆ (with x₆ x₄ = x₅² + 1 in the chain) has
support width exactly 6 > 4, and x₉ already has width 12; the widths
0, 2, 4, 6, 8, 10, 12 grow without bound along the chain. -/
theorem disproof_00000000570 :
    (∀ k, prodCoef TBL1 TBL3 k = prodCoef TBL2 TBL2 k + plus1 k) ∧
    (∀ k, prodCoef TBL2 TBL4 k = prodCoef TBL3 TBL3 k + plus1 k) ∧
    (∀ k, prodCoef TBL3 TBL5 k = prodCoef TBL4 TBL4 k + plus1 k) ∧
    (∀ k, prodCoef TBL4 TBL6 k = prodCoef TBL5 TBL5 k + plus1 k) ∧
    (∀ k, prodCoef TBL5 TBL7 k = prodCoef TBL6 TBL6 k + plus1 k) ∧
    (∀ k, prodCoef TBL6 TBL8 k = prodCoef TBL7 TBL7 k + plus1 k) ∧
    (∀ k, prodCoef TBL7 TBL9 k = prodCoef TBL8 TBL8 k + plus1 k) ∧
    (∀ k, coeffOf TBL6 k ≠ 0 → (-4 : Int) ≤ k.1 ∧ k.1 ≤ 2) ∧
    coeffOf TBL6 (-4, -3) ≠ 0 ∧ coeffOf TBL6 (2, -3) ≠ 0 ∧
    ((2 : Int) - (-4) = 6) ∧ (2 * 2 < 6) ∧
    (∀ k, coeffOf TBL9 k ≠ 0 → (-7 : Int) ≤ k.1 ∧ k.1 ≤ 5) ∧
    coeffOf TBL9 (-7, -6) ≠ 0 ∧ coeffOf TBL9 (5, -6) ≠ 0 ∧
    ((5 : Int) - (-7) = 12) ∧ (2 * 2 < 12) := by
  refine ⟨relz2, relz3, relz4, relz5, relz6, relz7, relz8, width6, ?_, ?_,
    rfl, by decide, width9, ?_, ?_, rfl, by decide⟩
  · decide
  · decide
  · decide
  · decide
