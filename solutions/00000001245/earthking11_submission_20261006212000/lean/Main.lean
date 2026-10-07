import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
Disproof of TLMC conjecture 00000001245 using the standard one-dimensional
elementary cellular automaton semantics.

An ECA rule is its Wolfram code in `Fin 256`. Neighborhoods are indexed by
their binary value `4*l + 2*c + r`, so the output is the corresponding bit of
the rule code. Configurations are functions `ℤ → Bool`; the global map applies
the local rule at every integer site. A finite output word is a GoE pattern
exactly when no bi-infinite configuration has an image containing that word
at any translated position.

Word density means the proportion of `true` symbols. Rule 255 is the constant
true local rule. The one-letter false word has no global preimage and density
zero. Every GoE word has nonnegative density. Consequently the set of actual
per-rule minimum densities has infimum zero; rules with no GoE words contribute
no minimum to that set.
-/

namespace TLMC1245

abbrev Rule := Fin 256
abbrev Config := ℤ → Bool

def bitValue (b : Bool) : ℕ := if b then 1 else 0

/-- The Wolfram neighborhood index, in binary order `111,...,000`. -/
def neighborhoodIndex (left center right : Bool) : Fin 8 :=
  ⟨4 * bitValue left + 2 * bitValue center + bitValue right, by
    cases left <;> cases center <;> cases right <;> norm_num [bitValue]⟩

/-- Decode one output bit of the Wolfram rule number. -/
def localOutput (rule : Rule) (left center right : Bool) : Bool :=
  Nat.testBit rule.val (neighborhoodIndex left center right).val

/-- The local cellular-automaton map on a two-sided configuration. -/
def globalOutput (rule : Rule) (x : Config) (site : ℤ) : Bool :=
  localOutput rule (x (site - 1)) (x site) (x (site + 1))

/-- A finite word occurs in the global output after some integer translation. -/
def HasFinitePreimage {n : ℕ} (rule : Rule) (word : Fin n → Bool) : Prop :=
  ∃ x : Config, ∃ start : ℤ,
    ∀ i : Fin n, globalOutput rule x (start + (i.val : ℤ)) = word i

/-- A nonempty finite output word with no bi-infinite preimage. -/
def IsGoE {n : ℕ} (rule : Rule) (word : Fin n → Bool) : Prop :=
  0 < n ∧ ¬ HasFinitePreimage rule word

/-- Proportion of `true` symbols in a finite word. -/
noncomputable def wordDensity {n : ℕ} (word : Fin n → Bool) : ℝ :=
  ((Finset.univ.filter fun i : Fin n => word i).card : ℝ) / (n : ℝ)

/-- The set of densities of genuine, nonempty GoE words for a fixed rule. -/
def goeDensities (rule : Rule) : Set ℝ :=
  {d | ∃ n : ℕ, ∃ word : Fin n → Bool,
      IsGoE rule word ∧ wordDensity word = d}

/-- A minimum is included only when it is attained by an actual GoE word.
    In particular, an ECA with no GoE words has no minimum-density value. -/
def IsMinimumDensity (rule : Rule) (d : ℝ) : Prop :=
  d ∈ goeDensities rule ∧ ∀ e ∈ goeDensities rule, d ≤ e

/-- Minimum densities taken over exactly those rules for which a minimum
    exists. Empty GoE sets contribute no value. -/
def AllMinimumDensities : Set ℝ :=
  {d | ∃ rule : Rule, IsMinimumDensity rule d}

def rule255 : Rule := ⟨255, by norm_num⟩
def rule133 : Rule := ⟨133, by norm_num⟩

theorem rule255_table (i : Fin 8) : Nat.testBit 255 i.val = true := by
  fin_cases i <;> decide

theorem localOutput_rule255 (left center right : Bool) :
    localOutput rule255 left center right = true := by
  unfold localOutput rule255
  exact rule255_table (neighborhoodIndex left center right)

theorem globalOutput_rule255 (x : Config) (site : ℤ) :
    globalOutput rule255 x site = true := by
  simp [globalOutput, localOutput_rule255]

def falseWord1 : Fin 1 → Bool := fun _ => false

theorem falseWord1_density : wordDensity falseWord1 = 0 := by
  norm_num [wordDensity, falseWord1]

theorem rule255_falseWord1_goe : IsGoE rule255 falseWord1 := by
  constructor
  · norm_num
  · intro hpre
    obtain ⟨x, start, h⟩ := hpre
    have h0 := h ⟨0, by omega⟩
    rw [globalOutput_rule255] at h0
    simp [falseWord1] at h0

theorem rule255_zero_is_minimum : IsMinimumDensity rule255 0 := by
  constructor
  · refine ⟨1, falseWord1, rule255_falseWord1_goe, falseWord1_density⟩
  · intro d hd
    rcases hd with ⟨n, word, hgoe, rfl⟩
    unfold wordDensity
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _

theorem minimum_of_empty_goe_set_is_absent (rule : Rule)
    (h : goeDensities rule = ∅) : ∀ d, ¬ IsMinimumDensity rule d := by
  intro d hd
  unfold IsMinimumDensity at hd
  rw [h] at hd
  exact hd.1.elim

theorem allMinimumDensities_nonempty : AllMinimumDensities.Nonempty := by
  exact ⟨0, rule255, rule255_zero_is_minimum⟩

theorem allMinimumDensities_nonneg : ∀ d ∈ AllMinimumDensities, 0 ≤ d := by
  intro d hd
  rcases hd with ⟨rule, hmin⟩
  rcases hmin.1 with ⟨n, word, hgoe, rfl⟩
  unfold wordDensity
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

/-- The infimum over all rules that actually have a minimum GoE density is zero.
    This treats the empty GoE set as having no minimum, not as a fabricated one. -/
theorem infimum_minimum_densities_eq_zero : sInf AllMinimumDensities = 0 := by
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, allMinimumDensities_nonneg⟩
    · exact ⟨rule255, rule255_zero_is_minimum⟩
  · exact Real.sInf_nonneg allMinimumDensities_nonneg

theorem conjectured_value_ne_actual_infimum :
    sInf AllMinimumDensities ≠ (1 / 4 : ℝ) := by
  rw [infimum_minimum_densities_eq_zero]
  norm_num

/-! ### Audit of the previous false witness

For rule 133, the finite input patch `1011` has neighborhoods `101` and `011`.
Both corresponding Wolfram output bits are zero, so `00` has a standard
bi-infinite preimage (extend the patch by zeros). This records why searching
only period-two cyclic preimages did not establish that `00` was a GoE word.
-/

def patch1011 (site : ℤ) : Bool := site = 0 ∨ site = 2 ∨ site = 3

theorem rule133_local_101_zero :
    localOutput rule133 true false true = false := by
  decide

theorem rule133_local_011_zero :
    localOutput rule133 false true true = false := by
  decide

theorem rule133_patch_outputs_00 :
    globalOutput rule133 patch1011 1 = false ∧
    globalOutput rule133 patch1011 2 = false := by
  constructor <;> norm_num [globalOutput, patch1011, localOutput,
    rule133, neighborhoodIndex, bitValue] <;> decide

theorem rule133_falseWord2_has_preimage :
    HasFinitePreimage rule133 (fun _ : Fin 2 => false) := by
  refine ⟨patch1011, 1, ?_⟩
  intro i
  fin_cases i
  · exact rule133_patch_outputs_00.1
  · simpa using rule133_patch_outputs_00.2

end TLMC1245

#print axioms TLMC1245.localOutput_rule255
#print axioms TLMC1245.rule255_falseWord1_goe
#print axioms TLMC1245.rule255_zero_is_minimum
#print axioms TLMC1245.infimum_minimum_densities_eq_zero
#print axioms TLMC1245.conjectured_value_ne_actual_infimum
#print axioms TLMC1245.rule133_falseWord2_has_preimage
