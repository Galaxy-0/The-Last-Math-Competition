import Std

/- Rank-one Weyl group: identity and the reflection r ↦ -r. -/
inductive W where | e | s
  deriving DecidableEq, Repr

def action : W → Int → Int
  | .e, r => r
  | .s, r => -r

def roots : Int → Prop := fun r => r = 1 ∨ r = -1
theorem reflection_preserves_roots (r : Int) (h : roots r) : roots (action .s r) := by
  rcases h with h | h <;> subst r <;> simp [roots, action]

def len : W → Nat | .e => 0 | .s => 1
def bruhat : W → W → Prop | .s, .e => False | _, _ => True
instance (x w : W) : Decidable (bruhat x w) := by cases x <;> cases w <;> unfold bruhat <;> infer_instance

/- A polynomial is its integer coefficient function with bounded support. -/
structure Poly where
  coeff : Nat → Int
  bound : Nat
  finite : ∀ k, bound < k → coeff k = 0

def one : Poly := ⟨fun k => if k = 0 then 1 else 0, 0, by
  intro k hk
  simp [Nat.ne_of_gt hk]⟩
def zero : Poly := ⟨fun _ => 0, 0, by intros; rfl⟩

/- These are defining KL normalization/degree properties, restricted to A1.
   The usual strict degree bound 2 deg P < l(w)-l(x) is stated coefficientwise.
   No property is postulated as an axiom: all are explicit hypotheses. -/
structure KLFamily (P : W → W → Poly) : Prop where
  outside : ∀ x w, ¬ bruhat x w → ∀ k, (P x w).coeff k = 0
  diagonal : ∀ x k, (P x x).coeff k = one.coeff k
  constant : ∀ x w, bruhat x w → (P x w).coeff 0 = 1
  degree : ∀ x w, x ≠ w → bruhat x w → ∀ k,
    len w - len x ≤ 2 * k → (P x w).coeff k = 0

def table : W → W → Poly | .s, .e => zero | _, _ => one

theorem table_is_KL : KLFamily table := by
  constructor
  · intro x w h k; cases x <;> cases w <;> simp_all [bruhat, table, zero]
  · intro x k; cases x <;> rfl
  · intro x w h; cases x <;> cases w <;> simp_all [bruhat, table, one]
  · intro x w hn hb k hk
    cases x <;> cases w <;> simp_all [bruhat, table, one, len]
    have h : k ≠ 0 := by omega
    simp [h]

theorem KL_unique_coeff (P : W → W → Poly) (h : KLFamily P)
    (x w : W) (k : Nat) : (P x w).coeff k = (table x w).coeff k := by
  cases x <;> cases w
  · exact h.diagonal .e k
  · cases k with
    | zero => exact h.constant .e .s True.intro
    | succ k =>
      have hz := h.degree .e .s (by decide) True.intro (k+1) (by simp [len]; omega)
      simpa [table, one] using hz
  · exact h.outside .s .e (by exact id) k
  · exact h.diagonal .s k

/- Leading coefficient excludes the zero polynomial: a nonzero coefficient
   with every higher coefficient zero. It is not a preassigned table entry. -/
def IsLeading (p : Poly) (k : Nat) : Prop :=
  p.coeff k ≠ 0 ∧ ∀ j, k < j → p.coeff j = 0

theorem leading_is_one (P : W → W → Poly) (h : KLFamily P)
    (x w : W) (k : Nat) (hl : IsLeading (P x w) k) : (P x w).coeff k = 1 := by
  have hc := KL_unique_coeff P h x w k
  have hn := hl.1
  cases x <;> cases w <;> simp_all [table, one, zero]

def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p
def OddPrimeDivisor (a : Int) : Prop :=
  ∃ p : Nat, Prime p ∧ p % 2 = 1 ∧ p ∣ a.natAbs

theorem one_has_no_prime_divisor : ¬ OddPrimeDivisor 1 := by
  intro ⟨p, hp, _, hd⟩
  have he : p = 1 := Nat.eq_one_of_dvd_one hd
  have := hp.1
  omega

theorem rank_one_disproof (P : W → W → Poly) (h : KLFamily P) :
    ¬ ∃ x w k, IsLeading (P x w) k ∧ OddPrimeDivisor ((P x w).coeff k) := by
  intro ⟨x, w, k, hl, hd⟩
  rw [leading_is_one P h x w k hl] at hd
  exact one_has_no_prime_divisor hd

theorem certified_counterexample :
    ¬ ∃ x w k, IsLeading (table x w) k ∧ OddPrimeDivisor ((table x w).coeff k) :=
  rank_one_disproof table table_is_KL

#print axioms KL_unique_coeff
#print axioms leading_is_one
#print axioms rank_one_disproof
#print axioms certified_counterexample
