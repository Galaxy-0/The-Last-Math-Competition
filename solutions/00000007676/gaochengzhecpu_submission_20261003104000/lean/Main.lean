import Std

/-! Conjecture 7676: the stated (major-index,descent) q-Eulerian polynomial
does not have the claimed standard gamma expansion, already for n = 2.
No gamma coefficient is asserted to be negative: no such expansion exists. -/

namespace Conjecture7676

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

abbrev Letter := Fin 2
abbrev Word := Letter × Letter

def wordMap (p : Word) (i : Letter) : Letter :=
  if i = 0 then p.1 else p.2

/-- A permutation means a bijective map on the two labels. -/
def IsPermutation (f : Letter → Letter) : Prop :=
  (∀ i j, f i = f j → i = j) ∧ (∀ y, ∃ x, f x = y)

def permutationWords : List Word := [(0,1), (1,0)]

theorem only_two_labels : ∀ i : Letter, i = 0 ∨ i = 1 := by decide

theorem exists_two (p : Letter → Prop) : (∃ i, p i) ↔ p 0 ∨ p 1 := by
  constructor
  · rintro ⟨i, hi⟩
    rcases only_two_labels i with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  · intro h
    rcases h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

/-- The two-position representation recovers every map, not only the listed ones. -/
theorem wordMap_encode (f : Letter → Letter) : wordMap (f 0, f 1) = f := by
  funext i
  rcases only_two_labels i with rfl | rfl <;> rfl

theorem encode_wordMap (p : Word) : (wordMap p 0, wordMap p 1) = p := by
  cases p
  rfl

theorem permutationWords_exact : ∀ p : Word,
    p ∈ permutationWords ↔ IsPermutation (wordMap p) := by
  have checked : ∀ a b : Letter,
      (a,b) ∈ permutationWords ↔ IsPermutation (wordMap (a,b)) := by
    simp only [IsPermutation, exists_two]
    decide
  intro p
  exact checked p.1 p.2

theorem permutationWords_nodup : permutationWords.Nodup := by decide

theorem all_permutations_represented (f : Letter → Letter)
    (hf : IsPermutation f) : (f 0, f 1) ∈ permutationWords := by
  apply (permutationWords_exact (f 0, f 1)).mpr
  rw [wordMap_encode]
  exact hf

theorem representation_injective (p r : Word)
    (h : wordMap p = wordMap r) : p = r := by
  have he := congrArg (fun f : Letter → Letter => (f 0, f 1)) h
  simpa only [encode_wordMap] using he

/-- Internal labels are 0,1; adding one gives the usual labels 1,2 and
preserves exactly the comparison defining the descent. -/
theorem usual_labels_same_order : ∀ a b : Letter,
    (a.val + 1 > b.val + 1) ↔ b < a := by decide

/-- There is only one possible descent position, with one-based index 1. -/
def descents (p : Word) : List Nat :=
  if p.2 < p.1 then [1] else []

def descentNumber (p : Word) : Nat := (descents p).length
def majorIndex (p : Word) : Nat := (descents p).sum

def qEulerian (words : List Word) (q t : Int) : Int :=
  (words.map (fun p => q ^ majorIndex p * t ^ descentNumber p)).sum

def eulerianTwo (q t : Int) : Int := qEulerian permutationWords q t

theorem statistics :
    permutationWords.map (fun p => (majorIndex p, descentNumber p)) =
      [(0,0),(1,1)] := by decide

theorem eulerianTwo_formula (q t : Int) : eulerianTwo q t = 1 + q * t := by
  simp [eulerianTwo, qEulerian, permutationWords, majorIndex, descentNumber,
    descents, List.sum_cons, Int.pow_succ]

/-- The coefficient list is in ascending degree order and consists of naturals,
so it represents an arbitrary polynomial in N[q]. -/
def evalNonnegativePolynomial : List Nat → Int → Int
  | [], _ => 0
  | a :: rest, q => Int.ofNat a + q * evalNonnegativePolynomial rest q

/-- A standard gamma expansion in degree n-1 has 0 <= j <= (n-1)/2. -/
def gammaSum (n : Nat) (gamma : Nat → List Nat) (q t : Int) : Int :=
  ((List.range ((n-1)/2+1)).map (fun j =>
    evalNonnegativePolynomial (gamma j) q * t^j * (1+t)^(n-1-2*j))).sum

theorem only_gamma_index_at_two (j : Nat) (h : 2*j ≤ 2-1) : j = 0 := by
  omega

theorem gammaSum_two (gamma : Nat → List Nat) (q t : Int) :
    gammaSum 2 gamma q t = evalNonnegativePolynomial (gamma 0) q * (1+t) := by
  simp [gammaSum, List.range_succ, List.sum_cons, Int.pow_succ]

/-- No scalar, even with unrestricted sign, works after specializing q=2. -/
theorem no_scalar_gamma_expansion :
    ¬ (∃ c : Int, ∀ t : Int, eulerianTwo 2 t = c * (1+t)) := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  rw [eulerianTwo_formula] at h0 h1
  simp at h0 h1
  omega

def HasNonnegativeGammaExpansionAtTwo : Prop :=
  ∃ gamma : Nat → List Nat, ∀ q t : Int,
    eulerianTwo q t = gammaSum 2 gamma q t

theorem no_nonnegative_gamma_expansion : ¬HasNonnegativeGammaExpansionAtTwo := by
  rintro ⟨gamma, hg⟩
  apply no_scalar_gamma_expansion
  refine ⟨evalNonnegativePolynomial (gamma 0) 2, ?_⟩
  intro t
  simpa only [gammaSum_two] using hg 2 t

/-- A complete, duplicate-free enumeration of the actual bijections S_2. -/
def FullPermutationEnumeration (words : List Word) : Prop :=
  words.Nodup ∧ ∀ p, p ∈ words ↔ IsPermutation (wordMap p)

theorem permutationWords_full : FullPermutationEnumeration permutationWords :=
  ⟨permutationWords_nodup, permutationWords_exact⟩

/-- The n=2 necessary instance of the original assertion, phrased using
any full enumeration of S_2. Polynomial identity implies these integer
evaluation identities, so ruling them out rules out the polynomial identity. -/
def Conjecture7676AtTwo : Prop :=
  ∃ gamma : Nat → List Nat, ∀ words, FullPermutationEnumeration words →
    ∀ q t : Int, qEulerian words q t = gammaSum 2 gamma q t

theorem conjecture7676_counterexample : ¬Conjecture7676AtTwo := by
  rintro ⟨gamma, h⟩
  apply no_nonnegative_gamma_expansion
  exact ⟨gamma, h permutationWords permutationWords_full⟩

#print axioms wordMap_encode
#print axioms permutationWords_exact
#print axioms all_permutations_represented
#print axioms representation_injective
#print axioms eulerianTwo_formula
#print axioms no_nonnegative_gamma_expansion
#print axioms conjecture7676_counterexample

end Conjecture7676
