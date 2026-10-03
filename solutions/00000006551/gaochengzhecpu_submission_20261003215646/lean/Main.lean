import Std
import Std.Internal.Rat

namespace FormalSplitting
abbrev Q := Std.Internal.Rat
abbrev Word := List Bool
abbrev Series := Word → Q
abbrev Stage := Bool × Q

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

def qpow (a : Q) : Nat → Q
  | 0 => 1
  | n+1 => a * qpow a n

/-- Coefficient of each noncommutative word in exp(a h A) or exp(a h B).
False denotes A and true denotes B; h-degree equals word length. -/
def exponential (letter : Bool) (a : Q) (w : Word) : Q :=
  if w.all (fun b => b == letter) then
    qpow a w.length / (OfNat.ofNat (factorial w.length) : Q)
  else 0

def sumTo (f : Nat → Q) : Nat → Q
  | 0 => 0
  | n+1 => sumTo f n + f n

/-- The genuine Cauchy product of two noncommutative formal series.
Every split w=prefix++suffix occurs exactly once. -/
def multiply (f g : Series) (w : Word) : Q :=
  sumTo (fun i => f (w.take i) * g (w.drop i)) (w.length+1)

theorem split_reconstruct (w : Word) (i : Nat) : w.take i ++ w.drop i = w :=
  List.take_append_drop i w
theorem split_complete (u v : Word) :
    (u++v).take u.length = u ∧ (u++v).drop u.length = v := by simp

def oneSeries (w : Word) : Q := if w.isEmpty then 1 else 0
def product : List Stage → Series
  | [] => oneSeries
  | (letter,a)::ss => multiply (exponential letter a) (product ss)

/-- exp(h(A+B)) has coefficient 1/n! on every word of length n. -/
def exactSeries (w : Word) : Q := 1 / (OfNat.ofNat (factorial w.length) : Q)

def PrefixEq (n : Nat) (f g : Series) : Prop :=
  ∀ w : Word, w.length ≤ n → f w = g w

theorem prefix_refl (n : Nat) (f : Series) : PrefixEq n f f := fun _ _ => rfl
theorem prefix_trans {n : Nat} {f g h : Series}
    (hfg : PrefixEq n f g) (hgh : PrefixEq n g h) : PrefixEq n f h :=
  fun w hw => (hfg w hw).trans (hgh w hw)

theorem sumTo_congr (f g : Nat → Q) (n : Nat)
    (h : ∀ i, i < n → f i = g i) : sumTo f n = sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumTo, sumTo, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem multiply_prefix {n : Nat} {f f' g g' : Series}
    (hf : PrefixEq n f f') (hg : PrefixEq n g g') :
    PrefixEq n (multiply f g) (multiply f' g') := by
  intro w hw
  apply sumTo_congr
  intro i _
  have ht : (w.take i).length ≤ n := by
    rw [List.length_take]
    exact Nat.le_trans (Nat.min_le_right _ _) hw
  have hd : (w.drop i).length ≤ n := by
    rw [List.length_drop]
    exact Nat.le_trans (Nat.sub_le _ _) hw
  rw [hf (w.take i) ht, hg (w.drop i) hd]

def wordCode : Word → Nat
  | [] => 0
  | a::w => 2 * wordCode w + if a then 2 else 1

def tableSeries (coefficients : List Q) (w : Word) : Q :=
  coefficients.getD (wordCode w) 0

def wordsFour : List Word :=
  [[], [false], [true], [false,false], [true,false], [false,true], [true,true],
   [false,false,false], [true,false,false], [false,true,false], [true,true,false],
   [false,false,true], [true,false,true], [false,true,true], [true,true,true],
   [false,false,false,false], [true,false,false,false], [false,true,false,false],
   [true,true,false,false], [false,false,true,false], [true,false,true,false],
   [false,true,true,false], [true,true,true,false], [false,false,false,true],
   [true,false,false,true], [false,true,false,true], [true,true,false,true],
   [false,false,true,true], [true,false,true,true], [false,true,true,true],
   [true,true,true,true]]

theorem wordsFour_complete (w : Word) (h : w.length ≤ 4) : w ∈ wordsFour := by
  cases w with
  | nil => decide
  | cons a w =>
    cases w with
    | nil => cases a <;> decide
    | cons b w =>
      cases w with
      | nil => cases a <;> cases b <;> decide
      | cons c w =>
        cases w with
        | nil => cases a <;> cases b <;> cases c <;> decide
        | cons d w =>
          cases w with
          | nil => cases a <;> cases b <;> cases c <;> cases d <;> decide
          | cons e w => simp only [List.length_cons] at h; omega

def prefixCheck (f g : Series) : Bool :=
  wordsFour.all (fun w => decide (f w = g w))

theorem checked_prefix (f g : Series) (h : prefixCheck f g = true) : PrefixEq 4 f g := by
  intro w hw
  have hh := List.all_eq_true.mp h w (wordsFour_complete w hw)
  exact of_decide_eq_true hh

def boundedCheck (n : Nat) (f g : Series) : Bool :=
  wordsFour.all (fun w => decide (w.length ≤ n → f w = g w))

theorem checked_bounded (n : Nat) (hn : n ≤ 4) (f g : Series)
    (h : boundedCheck n f g = true) : PrefixEq n f g := by
  intro w hw
  have hh := List.all_eq_true.mp h w (wordsFour_complete w (Nat.le_trans hw hn))
  exact (of_decide_eq_true hh) hw

/-- Substituting arbitrary values for words and taking any finite linear
combination respects coefficient equality. This includes evaluation in
every matrix or operator algebra; no commutativity is assumed. -/
def evaluateWords {R : Type} (zero : R) (add : R → R → R)
    (scale : Q → R → R) (value : Word → R) (s : Series) : List Word → R
  | [] => zero
  | w::ws => add (scale (s w) (value w)) (evaluateWords zero add scale value s ws)

theorem evaluation_congr {R : Type} (zero : R) (add : R → R → R)
    (scale : Q → R → R) (value : Word → R) {n : Nat} {f g : Series}
    (h : PrefixEq n f g) (ws : List Word) (bounded : ∀ w ∈ ws, w.length ≤ n) :
    evaluateWords zero add scale value f ws = evaluateWords zero add scale value g ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw := h w (bounded w (by simp))
    have ht : ∀ v ∈ ws, v.length ≤ n := by
      intro v hv
      exact bounded v (by simp [hv])
    simp only [evaluateWords, hw, ih ht]

def degreeWords (n : Nat) : List Word := wordsFour.filter (fun w => w.length == n)

theorem degreeWords_complete (n : Nat) (hn : n ≤ 4) (w : Word) :
    w ∈ degreeWords n ↔ w.length = n := by
  constructor
  · intro h
    have hh := (List.mem_filter.mp h).2
    exact of_decide_eq_true hh
  · intro h
    apply List.mem_filter.mpr
    exact ⟨wordsFour_complete w (by omega), by simp [h]⟩

theorem all_degree_evaluations {R : Type} (zero : R) (add : R → R → R)
    (scale : Q → R → R) (value : Word → R) {n : Nat} {f g : Series}
    (h : PrefixEq n f g) (d : Nat) (hd : d ≤ n) (hd4 : d ≤ 4) :
    evaluateWords zero add scale value f (degreeWords d) =
      evaluateWords zero add scale value g (degreeWords d) := by
  apply evaluation_congr zero add scale value h
  intro w hw
  have he := (degreeWords_complete d hd4 w).mp hw
  omega

def OrderAtLeast (n : Nat) (stages : List Stage) : Prop :=
  PrefixEq n (product stages) exactSeries

def commutator (w : Word) : Q :=
  if w = [false,true] then 1 else if w = [true,false] then -1 else 0

#print axioms multiply_prefix
#print axioms checked_prefix
end FormalSplitting

namespace Conjecture6551
open FormalSplitting

def stages : List Stage := [(false,3/4),(true,1),(false,1/4)]
def errorSeries (ss : List Stage) : Series := fun w => product ss w - exactSeries w
def ExactlyFirstOrder (ss : List Stage) : Prop :=
  OrderAtLeast 1 ss ∧ ¬OrderAtLeast 2 ss
def LeadingCoefficient (ss : List Stage) (c : Q) : Prop :=
  ∀ w, w.length = 2 → errorSeries ss w = c * commutator w

theorem order_one : OrderAtLeast 1 stages :=
  checked_bounded 1 (by decide) _ _ (by decide)

theorem order_one_after_arbitrary_substitution {R : Type} (zero : R) (add : R → R → R)
    (scale : Q → R → R) (value : Word → R) (d : Nat) (hd : d ≤ 1) :
    evaluateWords zero add scale value (product stages) (degreeWords d) =
      evaluateWords zero add scale value exactSeries (degreeWords d) :=
  all_degree_evaluations zero add scale value order_one d hd (by omega)

theorem degree_two_error : PrefixEq 2 (errorSeries stages)
    (fun w => (1/4 : Q) * commutator w) :=
  checked_bounded 2 (by decide) _ _ (by decide)

theorem not_order_two : ¬OrderAtLeast 2 stages := by
  intro h
  have hh := h [false,true] (by decide)
  have hn : product stages [false,true] ≠ exactSeries [false,true] := by decide
  exact hn hh

theorem exactly_first_order : ExactlyFirstOrder stages := ⟨order_one,not_order_two⟩

theorem leading_coefficient_quarter : LeadingCoefficient stages (1/4) :=
  fun w hw => degree_two_error w (by omega)

theorem leading_coefficient_unique (c : Q) (h : LeadingCoefficient stages c) :
    (1/4 : Q) = c * 1 := by
  have hh := h [false,true] rfl
  change (1/4 : Q) = c * 1 at hh
  exact hh

theorem leading_not_half : ¬LeadingCoefficient stages (1/2) := by
  intro h
  have hh := leading_coefficient_unique (1/2) h
  have hn : ¬((1/4 : Q) = (1/2 : Q) * 1) := by decide
  exact hn hh

theorem leading_not_negative_half : ¬LeadingCoefficient stages (-1/2) := by
  intro h
  have hh := leading_coefficient_unique (-1/2) h
  have hn : ¬((1/4 : Q) = (-1/2 : Q) * 1) := by decide
  exact hn hh

/-- Concrete noncommuting rational two-by-two operators. The coefficient
at degree two is evaluated from all four actual words, not a sampled entry. -/
abbrev Matrix := Fin 2 → Fin 2 → Q
def matMul (M N : Matrix) : Matrix := fun i j => M i 0 * N 0 j + M i 1 * N 1 j
def matOne : Matrix := fun i j => if i=j then 1 else 0
def matA : Matrix := fun i j => if i=0 ∧ j=1 then 1 else 0
def matB : Matrix := fun i j => if i=1 ∧ j=0 then 1 else 0
def evalWord : Word → Matrix
  | [] => matOne
  | a::w => matMul (if a then matB else matA) (evalWord w)
def degreeTwoEvaluation (s : Series) : Matrix := fun i j =>
  s [false,false] * evalWord [false,false] i j +
  s [false,true] * evalWord [false,true] i j +
  s [true,false] * evalWord [true,false] i j +
  s [true,true] * evalWord [true,true] i j
theorem matrices_noncommuting : ¬(∀ i j, matMul matA matB i j = matMul matB matA i j) := by decide
theorem actual_matrix_error : ∀ i j,
    degreeTwoEvaluation (errorSeries stages) i j =
      (1/4 : Q) * (matMul matA matB i j - matMul matB matA i j) := by decide
theorem actual_matrix_error_nonzero : degreeTwoEvaluation (errorSeries stages) 0 0 ≠ 0 := by decide

theorem conjecture6551_false :
    ¬(∀ ss : List Stage, ExactlyFirstOrder ss → LeadingCoefficient ss (1/2)) := by
  intro h
  exact leading_not_half (h stages exactly_first_order)

#print axioms order_one
#print axioms degree_two_error
#print axioms actual_matrix_error
#print axioms conjecture6551_false
end Conjecture6551
