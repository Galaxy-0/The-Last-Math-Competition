import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace Conjecture3944
abbrev Color := Fin 3
abbrev Vertex := Fin 8
abbrev Coloring := Vertex → Color

def adj (u v : Vertex) : Prop :=
 (u.val < 3 ∧ v.val < 3 ∧ u ≠ v) ∨
 (3 ≤ u.val ∧ u.val < 6 ∧ 3 ≤ v.val ∧ v.val < 6 ∧ u ≠ v) ∨
 (u.val < 3 ∧ v.val = u.val + 3) ∨
 (v.val < 3 ∧ u.val = v.val + 3) ∨
 (u = 0 ∧ 6 ≤ v.val) ∨ (v = 0 ∧ 6 ≤ u.val)
instance (u v : Vertex) : Decidable (adj u v) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))
def Proper (c : Coloring) : Prop := ∀ u v, adj u v → c u ≠ c v
instance (c : Coloring) : Decidable (Proper c) := inferInstanceAs (Decidable (∀ u v, adj u v → c u ≠ c v))
def eligible (c : Coloring) (a b : Color) (v : Vertex) : Prop := c v = a ∨ c v = b
instance (c : Coloring) (a b : Color) (v : Vertex) : Decidable (eligible c a b v) := inferInstanceAs (Decidable (_ ∨ _))
def swap (a b x : Color) : Color := if x = a then b else if x = b then a else x
def invariant (c : Coloring) : Prop := c 0 = c 4
instance (c : Coloring) : Decidable (invariant c) := inferInstanceAs (Decidable (c 0 = c 4))

def core (x0 x1 x2 x3 x4 x5 : Color) : Coloring := fun v =>
 match v.val with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | _ => x5
def sel (s0 s1 s2 s3 s4 s5 : Bool) : Vertex → Bool := fun v =>
 match v.val with | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | _ => s5
def CoreProper (c : Coloring) : Prop := ∀ u v : Fin 6, adj ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ → c ⟨u.val, by omega⟩ ≠ c ⟨v.val, by omega⟩
instance (c : Coloring) : Decidable (CoreProper c) := inferInstanceAs (Decidable (∀ u v : Fin 6, _))
def Closed (c : Coloring) (a b : Color) (s : Vertex → Bool) : Prop :=
 (∀ u : Fin 6, s ⟨u.val, by omega⟩ = true → eligible c a b ⟨u.val, by omega⟩) ∧
 (∀ u v : Fin 6, s ⟨u.val, by omega⟩ = true → adj ⟨u.val, by omega⟩ ⟨v.val, by omega⟩ → eligible c a b ⟨v.val, by omega⟩ → s ⟨v.val, by omega⟩ = true)
instance (c : Coloring) (a b : Color) (s : Vertex → Bool) : Decidable (Closed c a b s) := inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))
def switched (c : Coloring) (a b : Color) (s : Vertex → Bool) : Coloring := fun v => if s v then swap a b (c v) else c v

-- The only finite computation: six core colors, two selected colors and six membership bits.
theorem core_check : ∀ x0 x1 x2 x3 x4 x5 : Color,
 CoreProper (core x0 x1 x2 x3 x4 x5) → ∀ a b : Color,
 ∀ s0 s1 s2 s3 s4 s5 : Bool,
 Closed (core x0 x1 x2 x3 x4 x5) a b (sel s0 s1 s2 s3 s4 s5) →
 (invariant (core x0 x1 x2 x3 x4 x5) ↔ invariant (switched (core x0 x1 x2 x3 x4 x5) a b (sel s0 s1 s2 s3 s4 s5))) := by decide +kernel



theorem core_agrees (c : Coloring) (v : Vertex) (hv : v.val < 6) :
 core (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) v = c v := by
 have h : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by
  simp only [Fin.ext_iff]
  omega
 rcases h with h | h | h | h | h | h <;> subst v <;> rfl

theorem sel_agrees (s : Vertex → Bool) (v : Vertex) (hv : v.val < 6) :
 sel (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) v = s v := by
 have h : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by
  simp only [Fin.ext_iff]
  omega
 rcases h with h | h | h | h | h | h <;> subst v <;> rfl

theorem invariant_switch (c : Coloring) (hc : Proper c) (a b : Color)
 (s : Vertex → Bool) (hs : Closed c a b s) :
 invariant c ↔ invariant (switched c a b s) := by
 have hp : CoreProper (core (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)) := by
  intro u v h
  rw [core_agrees _ _ u.isLt, core_agrees _ _ v.isLt]
  exact hc _ _ h
 have hclosed : Closed (core (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)) a b
   (sel (s 0) (s 1) (s 2) (s 3) (s 4) (s 5)) := by
  constructor
  · intro u hu
    rw [sel_agrees _ _ u.isLt] at hu
    unfold eligible
    rw [core_agrees _ _ u.isLt]
    exact hs.1 u hu
  · intro u v hu huv hv
    rw [sel_agrees _ _ u.isLt] at hu
    unfold eligible at hv
    rw [core_agrees _ _ v.isLt] at hv
    rw [sel_agrees _ _ v.isLt]
    exact hs.2 u v hu huv hv
 exact core_check (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) hp a b
   (s 0) (s 1) (s 2) (s 3) (s 4) (s 5) hclosed

/-- Paths in the subgraph induced by the two chosen colors. -/
inductive Chain (c : Coloring) (a b : Color) (seed : Vertex) : Vertex → Prop
| root : eligible c a b seed → Chain c a b seed seed
| step {u v : Vertex} : Chain c a b seed u → adj u v → eligible c a b v → Chain c a b seed v

theorem chain_eligible {c : Coloring} {a b : Color} {seed v : Vertex}
 (h : Chain c a b seed v) : eligible c a b v := by
 cases h with
 | root h => exact h
 | step _ _ h => exact h

/-- A legal switch flips the entire connected component containing seed. -/
def KempeMove (c d : Coloring) : Prop := ∃ a b : Color, a ≠ b ∧ ∃ seed : Vertex,
 eligible c a b seed ∧ ∀ v, (Chain c a b seed v → d v = swap a b (c v)) ∧
 (¬ Chain c a b seed v → d v = c v)

theorem kempe_invariant {c d : Coloring} (hc : Proper c) (h : KempeMove c d) :
 invariant c ↔ invariant d := by
 classical
 rcases h with ⟨a, b, _, seed, _, hd⟩
 let s : Vertex → Bool := fun v => decide (Chain c a b seed v)
 have hs : Closed c a b s := by
  constructor
  · intro u hu
    exact chain_eligible (of_decide_eq_true hu)
  · intro u v hu huv hv
    exact decide_eq_true (Chain.step (of_decide_eq_true hu) huv hv)
 have heq : switched c a b s = d := by
  funext v
  by_cases h : Chain c a b seed v
  · simp [switched, s, h, (hd v).1 h]
  · simp [switched, s, h, (hd v).2 h]
 rw [← heq]
 exact invariant_switch c hc a b s hs



/-- Base-three coding, with all eight vertex coordinates retained. -/
abbrev Code := Fin 6561
def decode (x : Code) : Coloring := fun v => ⟨(x.val / 3^v.val) % 3, Nat.mod_lt _ (by decide +kernel)⟩
def encode (c : Coloring) : Code :=
 ⟨(c 0).val + 3*(c 1).val + 9*(c 2).val + 27*(c 3).val + 81*(c 4).val + 243*(c 5).val + 729*(c 6).val + 2187*(c 7).val, by
  have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt; have h3 := (c 3).isLt
  have h4 := (c 4).isLt; have h5 := (c 5).isLt; have h6 := (c 6).isLt; have h7 := (c 7).isLt
  omega⟩
theorem decode_encode (c : Coloring) : decode (encode c) = c := by
 funext v
 have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt; have h3 := (c 3).isLt
 have h4 := (c 4).isLt; have h5 := (c 5).isLt; have h6 := (c 6).isLt; have h7 := (c 7).isLt
 have h : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by
  simp only [Fin.ext_iff]
  have := v.isLt
  omega
 rcases h with h | h | h | h | h | h | h | h <;> subst v
 · apply Fin.ext
   change (((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val + 81 * (c 4).val + 243 * (c 5).val + 729 * (c 6).val + 2187 * (c 7).val) / 1) % 3 = (c 0).val
   omega
 · apply Fin.ext
   change (((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val + 81 * (c 4).val + 243 * (c 5).val + 729 * (c 6).val + 2187 * (c 7).val) / 3) % 3 = (c 1).val
   omega
 · apply Fin.ext
   change (((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val + 81 * (c 4).val + 243 * (c 5).val + 729 * (c 6).val + 2187 * (c 7).val) / 9) % 3 = (c 2).val
   omega
 · apply Fin.ext
   change (((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val + 81 * (c 4).val + 243 * (c 5).val + 729 * (c 6).val + 2187 * (c 7).val) / 27) % 3 = (c 3).val
   omega
 · apply Fin.ext
   change (((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val + 81 * (c 4).val + 243 * (c 5).val + 729 * (c 6).val + 2187 * (c 7).val) / 81) % 3 = (c 4).val
   omega
 · apply Fin.ext
   change (((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val + 81 * (c 4).val + 243 * (c 5).val + 729 * (c 6).val + 2187 * (c 7).val) / 243) % 3 = (c 5).val
   omega
 · apply Fin.ext
   change (((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val + 81 * (c 4).val + 243 * (c 5).val + 729 * (c 6).val + 2187 * (c 7).val) / 729) % 3 = (c 6).val
   omega
 · apply Fin.ext
   change (((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val + 81 * (c 4).val + 243 * (c 5).val + 729 * (c 6).val + 2187 * (c 7).val) / 2187) % 3 = (c 7).val
   omega


theorem decode_injective (x y : Code) (h : decode x = decode y) : x = y := by
 have h0 := congrArg (fun c : Coloring => (c 0).val) h
 have h1 := congrArg (fun c : Coloring => (c 1).val) h
 have h2 := congrArg (fun c : Coloring => (c 2).val) h
 have h3 := congrArg (fun c : Coloring => (c 3).val) h
 have h4 := congrArg (fun c : Coloring => (c 4).val) h
 have h5 := congrArg (fun c : Coloring => (c 5).val) h
 have h6 := congrArg (fun c : Coloring => (c 6).val) h
 have h7 := congrArg (fun c : Coloring => (c 7).val) h
 change (x.val / 1) % 3 = (y.val / 1) % 3 at h0
 change (x.val / 3) % 3 = (y.val / 3) % 3 at h1
 change (x.val / 9) % 3 = (y.val / 9) % 3 at h2
 change (x.val / 27) % 3 = (y.val / 27) % 3 at h3
 change (x.val / 81) % 3 = (y.val / 81) % 3 at h4
 change (x.val / 243) % 3 = (y.val / 243) % 3 at h5
 change (x.val / 729) % 3 = (y.val / 729) % 3 at h6
 change (x.val / 2187) % 3 = (y.val / 2187) % 3 at h7
 apply Fin.ext
 have := x.isLt; have := y.isLt
 omega

def states : List Code := (List.finRange 6561).filter (fun x => decide (Proper (decode x)))
theorem states_complete (x : Code) : x ∈ states ↔ Proper (decode x) := by
 simp [states, List.mem_finRange]
theorem state_count : states.length = 48 := by decide +kernel

def first : Code := 3126
def second : Code := 3234
theorem first_proper : Proper (decode first) := by decide +kernel
theorem second_proper : Proper (decode second) := by decide +kernel
theorem first_class : ¬ invariant (decode first) := by decide +kernel
theorem second_class : invariant (decode second) := by decide +kernel

def degree (v : Vertex) : Nat := ((List.finRange 8).filter (fun u => decide (adj v u))).length
theorem simple_graph : (∀ v, ¬ adj v v) ∧ (∀ u v, adj u v ↔ adj v u) := by decide +kernel
theorem degree_five : degree 0 = 5 ∧ ∀ v, degree v ≤ 5 := by decide +kernel

inductive Walk : Vertex → Vertex → Prop
| refl (v) : Walk v v
| step {u v w} : Walk u v → adj v w → Walk u w

theorem connected : ∀ v, Walk 0 v := by
 intro v
 have h : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 := by
  simp only [Fin.ext_iff]
  have := v.isLt
  omega
 rcases h with h | h | h | h | h | h | h | h <;> subst v
 · exact Walk.refl 0
 · exact Walk.step (Walk.refl 0) (by decide +kernel)
 · exact Walk.step (Walk.refl 0) (by decide +kernel)
 · exact Walk.step (Walk.refl 0) (by decide +kernel)
 · exact Walk.step (Walk.step (Walk.refl 0) (show adj 0 1 by decide +kernel)) (by decide +kernel)
 · exact Walk.step (Walk.step (Walk.refl 0) (show adj 0 2 by decide +kernel)) (by decide +kernel)
 · exact Walk.step (Walk.refl 0) (by decide +kernel)
 · exact Walk.step (Walk.refl 0) (by decide +kernel)

/-- Allowed transition includes optional laziness. -/
def Allowed (x y : Code) : Prop := x = y ∨ KempeMove (decode x) (decode y)
theorem allowed_invariant {x y : Code} (hx : x ∈ states) (h : Allowed x y) :
 invariant (decode x) ↔ invariant (decode y) := by
 rcases h with h | h
 · subst y; exact Iff.rfl
 · exact kempe_invariant ((states_complete x).mp hx) h

inductive Steps : Code → Code → Prop
| refl (x) : Steps x x
| step {x y z} : Steps x y → y ∈ states → Allowed y z → Steps x z

theorem steps_invariant {x y : Code} (h : Steps x y) : invariant (decode x) ↔ invariant (decode y) := by
 induction h with
 | refl => exact Iff.rfl
 | step _ hy hstep ih => exact ih.trans (allowed_invariant hy hstep)

theorem unreachable : ¬ Steps first second := by
 intro h
 exact first_class ((steps_invariant h).mpr second_class)

/-- Transition kernels may use any rational probabilities; the result is stronger
than required because stochastic normalization is not needed for the obstruction. -/
def Supported (P : Code → Code → Rat) : Prop := ∀ x ∈ states, ∀ y ∈ states, ¬ Allowed x y → P x y = 0

def law (P : Code → Code → Rat) : Nat → Code → Rat
| 0, y => if y = first then 1 else 0
| n+1, y => (states.map (fun x => law P n x * P x y)).sum

theorem sum_map_zero {α : Type} (xs : List α) (f : α → Rat)
 (h : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
 induction xs with
 | nil => rfl
 | cons a xs ih =>
  simp only [List.map_cons, List.sum_cons]
  rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]
  exact Rat.add_zero 0

theorem law_vanishes (P : Code → Code → Rat) (hp : Supported P) :
 ∀ n y, y ∈ states → invariant (decode y) → law P n y = 0 := by
 intro n
 induction n with
 | zero =>
  intro y hy hclass
  have hne : y ≠ first := by
   intro h; subst y; exact first_class hclass
  simp [law, hne]
 | succ n ih =>
  intro y hy hclass
  apply sum_map_zero
  intro x hx
  by_cases hc : invariant (decode x)
  · rw [ih x hx hc, Rat.zero_mul]
  · have hno : ¬ Allowed x y := fun h => hc ((allowed_invariant hx h).mpr hclass)
    rw [hp x hx y hy hno, Rat.mul_zero]

def uniform (y : Code) : Rat := if Proper (decode y) then 1/48 else 0

theorem uniform_mass (y : Code) (hy : y ∈ states) : uniform y = 1/(states.length : Rat) := by
 rw [state_count]
 simp [uniform, (states_complete y).mp hy]

theorem uniform_normalized : (states.map uniform).sum = 1 := by decide +kernel

theorem uniform_second : uniform second = 1/48 := by decide +kernel

theorem separation (P : Code → Code → Rat) (hp : Supported P) (n : Nat) :
 (law P n second - uniform second).abs = 1/48 := by
 rw [law_vanishes P hp n second ((states_complete second).mpr second_proper) second_class, uniform_second]
 decide +kernel

/-- Pointwise convergence on this finite state space, using rational epsilons. -/
def ConvergesToUniform (P : Code → Code → Rat) : Prop :=
 ∀ ε : Rat, 0 < ε → ∃ N : Nat, ∀ n, N ≤ n → ∀ y ∈ states,
 (law P n y - uniform y).abs < ε

theorem no_uniform_mixing (P : Code → Code → Rat) (hp : Supported P) : ¬ ConvergesToUniform P := by
 intro h
 obtain ⟨N, hN⟩ := h (1/96) (by decide +kernel)
 have bad := hN N (Nat.le_refl N) second ((states_complete second).mpr second_proper)
 rw [separation P hp N] at bad
 exact (by decide +kernel : ¬ (1/48 : Rat) < 1/96) bad



/-- Total variation is the supremum of discrepancies on events. -/
def eventMass (μ : Code → Rat) (A : Code → Bool) : Rat :=
 ((states.filter A).map μ).sum

def opposite : Code → Bool := fun y => decide (invariant (decode y))
theorem opposite_count : (states.filter opposite).length = 24 := by decide +kernel

theorem opposite_uniform : eventMass uniform opposite = 1/2 := by decide +kernel

theorem opposite_zero (P : Code → Code → Rat) (hp : Supported P) (n : Nat) :
 eventMass (law P n) opposite = 0 := by
 apply sum_map_zero
 intro y hy
 obtain ⟨hys, hyo⟩ := List.mem_filter.mp hy
 exact law_vanishes P hp n y hys (of_decide_eq_true hyo)

theorem event_gap (P : Code → Code → Rat) (hp : Supported P) (n : Nat) :
 (eventMass (law P n) opposite - eventMass uniform opposite).abs = 1/2 := by
 rw [opposite_zero P hp n, opposite_uniform]
 decide +kernel

def WithinQuarter (μ ν : Code → Rat) : Prop := ∀ A : Code → Bool,
 (eventMass μ A - eventMass ν A).abs ≤ 1/4

theorem never_mixes_at_quarter (P : Code → Code → Rat) (hp : Supported P) (n : Nat) :
 ¬ WithinQuarter (law P n) uniform := by
 intro h
 have bad := h opposite
 rw [event_gap P hp n] at bad
 exact (by decide +kernel : ¬ (1/2 : Rat) ≤ 1/4) bad

/-- The standard finite-state stochastic-kernel conditions. -/
def Stochastic (P : Code → Code → Rat) : Prop := ∀ x ∈ states,
 (∀ y ∈ states, 0 ≤ P x y) ∧ (states.map (P x)).sum = 1

/-- The asserted Δ ≥ 5 mixing conclusion already fails on this connected graph. -/
theorem counterexample :
 (∀ v, Walk 0 v) ∧ (degree 0 = 5 ∧ ∀ v, degree v ≤ 5) ∧
 ∀ P : Code → Code → Rat, Stochastic P → Supported P →
 ∀ n : Nat, ¬ WithinQuarter (law P n) uniform := by
 refine ⟨connected, degree_five, ?_⟩
 intro P _ hp n
 exact never_mixes_at_quarter P hp n

#print axioms core_check
#print axioms kempe_invariant
#print axioms decode_encode
#print axioms decode_injective
#print axioms state_count
#print axioms connected
#print axioms degree_five
#print axioms unreachable
#print axioms no_uniform_mixing
#print axioms never_mixes_at_quarter
#print axioms counterexample
end Conjecture3944
