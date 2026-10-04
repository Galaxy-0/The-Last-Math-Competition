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

namespace Conjecture6557
open FormalSplitting
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def stages : List Stage := [(false,(1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]
def table0 : Series := tableSeries [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def table1 : Series := tableSeries [1,(1/12),0,(1/288),0,0,0,(1/10368),0,0,0,0,0,0,0,(1/497664),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def table2 : Series := tableSeries [1,(1/12),(1/6),(1/288),(1/72),0,(1/72),(1/10368),(1/1728),0,(1/864),0,0,0,(1/1296),(1/497664),(1/62208),0,(1/20736),0,0,0,(1/15552),0,0,0,0,0,0,0,(1/31104)]
def table3 : Series := tableSeries [1,(1/4),(1/6),(1/32),(1/72),(1/36),(1/72),(1/384),(1/1728),(1/432),(1/864),(1/432),0,(1/432),(1/1296),(1/6144),(1/62208),(1/10368),(1/20736),(1/5184),0,(1/5184),(1/15552),(1/7776),0,0,0,(1/5184),0,(1/7776),(1/31104)]
def table4 : Series := tableSeries [1,(1/4),(1/3),(1/32),(1/18),(1/36),(1/18),(1/384),(5/864),(1/432),(1/144),(1/432),(1/216),(1/432),(1/162),(1/6144),(7/15552),(1/10368),(1/1728),(1/5184),(1/2592),(1/5184),(5/7776),(1/7776),(1/2592),0,(1/2592),(1/5184),(1/2592),(1/7776),(1/1944)]
def table5 : Series := tableSeries [1,(5/12),(1/3),(25/288),(1/18),(1/12),(1/18),(125/10368),(5/864),(5/432),(1/144),(5/432),(1/216),(5/432),(1/162),(625/497664),(7/15552),(11/10368),(1/1728),(7/5184),(1/2592),(7/5184),(5/7776),(1/864),(1/2592),(1/1296),(1/2592),(7/5184),(1/2592),(1/864),(1/1944)]
def table6 : Series := tableSeries [1,(5/12),(1/2),(25/288),(1/8),(1/12),(1/8),(125/10368),(35/1728),(5/432),(19/864),(5/432),(1/54),(5/432),(1/48),(625/497664),(17/6912),(11/10368),(19/6912),(7/5184),(1/432),(7/5184),(5/1728),(1/864),(1/432),(1/1296),(1/432),(7/5184),(1/432),(1/864),(1/384)]
def table7 : Series := tableSeries [1,(7/12),(1/2),(49/288),(1/8),(1/6),(1/8),(343/10368),(35/1728),(7/216),(19/864),(7/216),(1/54),(7/216),(1/48),(2401/497664),(17/6912),(23/5184),(19/6912),(13/2592),(1/432),(13/2592),(5/1728),(1/216),(1/432),(5/1296),(1/432),(13/2592),(1/432),(1/216),(1/384)]
def table8 : Series := tableSeries [1,(7/12),(2/3),(49/288),(2/9),(1/6),(2/9),(343/10368),(7/144),(7/216),(11/216),(7/216),(5/108),(7/216),(4/81),(2401/497664),(31/3888),(23/5184),(11/1296),(13/2592),(5/648),(13/2592),(17/1944),(1/216),(5/648),(5/1296),(5/648),(13/2592),(5/648),(1/216),(2/243)]
def table9 : Series := tableSeries [1,(1/2),(2/3),(1/8),(2/9),(1/9),(2/9),(1/48),(7/144),(1/72),(11/216),(1/48),(5/108),(1/72),(4/81),(1/384),(31/3888),(1/2592),(11/1296),(1/324),(5/648),(1/1296),(17/1944),(19/7776),(5/648),0,(5/648),(1/324),(5/648),(1/1944),(2/243)]
def table10 : Series := tableSeries [1,(1/2),(1/3),(1/8),(1/18),(1/9),(1/18),(1/48),(1/144),(1/72),(1/216),(1/48),(1/108),(1/72),(1/162),(1/384),(1/972),(1/2592),(-1/1296),(1/324),(1/324),(1/1296),(1/972),(19/7776),(1/1296),0,(-1/648),(1/324),(1/324),(1/1944),(1/1944)]
def table11 : Series := tableSeries [1,(5/12),(1/3),(25/288),(1/18),(1/12),(1/18),(125/10368),(1/144),(1/108),(1/216),(11/864),(1/108),(1/108),(1/162),(625/497664),(1/972),(-1/5184),(-1/1296),(11/5184),(1/324),(1/2592),(1/972),(11/10368),(1/1296),(-1/1296),(-1/648),(11/5184),(1/324),0,(1/1944)]
def table12 : Series := tableSeries [1,(5/12),(1/2),(25/288),(1/8),(1/12),(1/8),(125/10368),(37/1728),(1/108),(17/864),(11/864),(5/216),(1/108),(1/48),(625/497664),(7/2304),(-1/5184),(11/6912),(11/5184),(1/216),(1/2592),(5/1728),(11/10368),(5/1728),(-1/1296),(1/864),(11/5184),(1/216),0,(1/384)]
def table13 : Series := tableSeries [1,(7/12),(1/2),(49/288),(1/8),(1/6),(1/8),(343/10368),(37/1728),(13/432),(17/864),(29/864),(5/216),(13/432),(1/48),(2401/497664),(7/2304),(35/10368),(11/6912),(7/1296),(1/216),(19/5184),(5/1728),(49/10368),(5/1728),(1/324),(1/864),(7/1296),(1/216),(1/288),(1/384)]
def table14 : Series := tableSeries [1,(7/12),(2/3),(49/288),(2/9),(1/6),(2/9),(343/10368),(43/864),(13/432),(7/144),(29/864),(11/216),(13/432),(4/81),(2401/497664),(133/15552),(35/10368),(13/1728),(7/1296),(25/2592),(19/5184),(65/7776),(49/10368),(11/1296),(1/324),(19/2592),(7/1296),(25/2592),(1/288),(2/243)]
def table15 : Series := tableSeries [1,(3/4),(2/3),(9/32),(2/9),(5/18),(2/9),(9/128),(43/864),(29/432),(7/144),(61/864),(11/216),(29/432),(4/81),(27/2048),(133/15552),(121/10368),(13/1728),(35/2592),(25/2592),(61/5184),(65/7776),(409/31104),(11/1296),(5/432),(19/2592),(35/2592),(25/2592),(91/7776),(2/243)]
def table16 : Series := tableSeries [1,(3/4),(5/6),(9/32),(25/72),(5/18),(25/72),(9/128),(167/1728),(29/432),(83/864),(61/864),(7/72),(29/432),(125/1296),(27/2048),(1261/62208),(121/10368),(409/20736),(35/2592),(1/48),(61/5184),(313/15552),(409/31104),(35/1728),(5/432),(17/864),(35/2592),(1/48),(91/7776),(625/31104)]
def table17 : Series := tableSeries [1,(11/12),(5/6),(121/288),(25/72),(5/12),(25/72),(1331/10368),(167/1728),(1/8),(83/864),(37/288),(7/72),(1/8),(125/1296),(14641/497664),(1261/62208),(1/36),(409/20736),(17/576),(1/48),(1/36),(313/15552),(305/10368),(35/1728),(1/36),(17/864),(17/576),(1/48),(1/36),(625/31104)]
def table18 : Series := tableSeries [1,(11/12),1,(121/288),(1/2),(5/12),(1/2),(1331/10368),(1/6),(1/8),(1/6),(37/288),(1/6),(1/8),(1/6),(14641/497664),(1/24),(1/36),(1/24),(17/576),(1/24),(1/36),(1/24),(305/10368),(1/24),(1/36),(1/24),(17/576),(1/24),(1/36),(1/24)]
def table19 : Series := tableSeries [1,1,1,(1/2),(1/2),(1/2),(1/2),(1/6),(1/6),(1/6),(1/6),(1/6),(1/6),(1/6),(1/6),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24),(1/24)]
theorem prefix0 : PrefixEq 4 (product []) table0 := checked_prefix _ _ (by decide)
theorem table_step1 : PrefixEq 4 (multiply (exponential false (1/12)) table0) table1 :=
  checked_prefix _ _ (by decide)
theorem prefix1 : PrefixEq 4 (product [(false,(1/12))]) table1 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix0) table_step1
theorem table_step2 : PrefixEq 4 (multiply (exponential true (1/6)) table1) table2 :=
  checked_prefix _ _ (by decide)
theorem prefix2 : PrefixEq 4 (product [(true,(1/6)),(false,(1/12))]) table2 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix1) table_step2
theorem table_step3 : PrefixEq 4 (multiply (exponential false (1/6)) table2) table3 :=
  checked_prefix _ _ (by decide)
theorem prefix3 : PrefixEq 4 (product [(false,(1/6)),(true,(1/6)),(false,(1/12))]) table3 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix2) table_step3
theorem table_step4 : PrefixEq 4 (multiply (exponential true (1/6)) table3) table4 :=
  checked_prefix _ _ (by decide)
theorem prefix4 : PrefixEq 4 (product [(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table4 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix3) table_step4
theorem table_step5 : PrefixEq 4 (multiply (exponential false (1/6)) table4) table5 :=
  checked_prefix _ _ (by decide)
theorem prefix5 : PrefixEq 4 (product [(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table5 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix4) table_step5
theorem table_step6 : PrefixEq 4 (multiply (exponential true (1/6)) table5) table6 :=
  checked_prefix _ _ (by decide)
theorem prefix6 : PrefixEq 4 (product [(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table6 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix5) table_step6
theorem table_step7 : PrefixEq 4 (multiply (exponential false (1/6)) table6) table7 :=
  checked_prefix _ _ (by decide)
theorem prefix7 : PrefixEq 4 (product [(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table7 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix6) table_step7
theorem table_step8 : PrefixEq 4 (multiply (exponential true (1/6)) table7) table8 :=
  checked_prefix _ _ (by decide)
theorem prefix8 : PrefixEq 4 (product [(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table8 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix7) table_step8
theorem table_step9 : PrefixEq 4 (multiply (exponential false (-1/12)) table8) table9 :=
  checked_prefix _ _ (by decide)
theorem prefix9 : PrefixEq 4 (product [(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table9 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix8) table_step9
theorem table_step10 : PrefixEq 4 (multiply (exponential true (-1/3)) table9) table10 :=
  checked_prefix _ _ (by decide)
theorem prefix10 : PrefixEq 4 (product [(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table10 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix9) table_step10
theorem table_step11 : PrefixEq 4 (multiply (exponential false (-1/12)) table10) table11 :=
  checked_prefix _ _ (by decide)
theorem prefix11 : PrefixEq 4 (product [(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table11 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix10) table_step11
theorem table_step12 : PrefixEq 4 (multiply (exponential true (1/6)) table11) table12 :=
  checked_prefix _ _ (by decide)
theorem prefix12 : PrefixEq 4 (product [(true,(1/6)),(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table12 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix11) table_step12
theorem table_step13 : PrefixEq 4 (multiply (exponential false (1/6)) table12) table13 :=
  checked_prefix _ _ (by decide)
theorem prefix13 : PrefixEq 4 (product [(false,(1/6)),(true,(1/6)),(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table13 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix12) table_step13
theorem table_step14 : PrefixEq 4 (multiply (exponential true (1/6)) table13) table14 :=
  checked_prefix _ _ (by decide)
theorem prefix14 : PrefixEq 4 (product [(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table14 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix13) table_step14
theorem table_step15 : PrefixEq 4 (multiply (exponential false (1/6)) table14) table15 :=
  checked_prefix _ _ (by decide)
theorem prefix15 : PrefixEq 4 (product [(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table15 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix14) table_step15
theorem table_step16 : PrefixEq 4 (multiply (exponential true (1/6)) table15) table16 :=
  checked_prefix _ _ (by decide)
theorem prefix16 : PrefixEq 4 (product [(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table16 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix15) table_step16
theorem table_step17 : PrefixEq 4 (multiply (exponential false (1/6)) table16) table17 :=
  checked_prefix _ _ (by decide)
theorem prefix17 : PrefixEq 4 (product [(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table17 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix16) table_step17
theorem table_step18 : PrefixEq 4 (multiply (exponential true (1/6)) table17) table18 :=
  checked_prefix _ _ (by decide)
theorem prefix18 : PrefixEq 4 (product [(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table18 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix17) table_step18
theorem table_step19 : PrefixEq 4 (multiply (exponential false (1/12)) table18) table19 :=
  checked_prefix _ _ (by decide)
theorem prefix19 : PrefixEq 4 (product [(false,(1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(-1/12)),(true,(-1/3)),(false,(-1/12)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/6)),(true,(1/6)),(false,(1/12))]) table19 := by
  exact prefix_trans (multiply_prefix (prefix_refl 4 _) prefix18) table_step19
theorem final_table_exact : PrefixEq 4 table19 exactSeries := checked_prefix _ _ (by decide)
theorem order_four : OrderAtLeast 4 stages := prefix_trans prefix19 final_table_exact
theorem order_four_after_arbitrary_substitution {R : Type} (zero : R) (add : R → R → R)
    (scale : Q → R → R) (value : Word → R) (d : Nat) (hd : d ≤ 4) :
    evaluateWords zero add scale value (product stages) (degreeWords d) =
      evaluateWords zero add scale value exactSeries (degreeWords d) :=
  all_degree_evaluations zero add scale value order_four d hd hd
theorem all_stages_nonzero : ∀ p ∈ stages, p.2 ≠ 0 := by decide
theorem stages_alternate : stages.map Prod.fst = [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] := by decide
def coefficientSum (letter : Bool) (ss : List Stage) : Q := ((ss.filter (fun p => p.1 == letter)).map Prod.snd).foldr (· + ·) 0
theorem consistent_sums : coefficientSum false stages = 1 ∧ coefficientSum true stages = 1 := by decide
def negativeSum (ss : List Stage) : Q := ((ss.filter (fun p => p.2 < 0)).map Prod.snd).foldr (· + ·) 0
def negativeMagnitudeSum (ss : List Stage) : Q := ((ss.filter (fun p => p.2 < 0)).map (fun p => -p.2)).foldr (· + ·) 0
theorem signed_negative_sum : negativeSum stages = (-1/2 : Q) := by decide
theorem negative_magnitude_sum : negativeMagnitudeSum stages = (1/2 : Q) := by decide
theorem has_negative : ∃ p ∈ stages, p.2 < 0 := by decide
theorem negative_sum_not_one : negativeSum stages ≠ 1 := by decide
theorem negative_magnitude_not_one : negativeMagnitudeSum stages ≠ 1 := by decide
theorem conjecture6557_false : ¬(∀ ss : List Stage, OrderAtLeast 4 ss → negativeSum ss = 1) := by
  intro h; exact negative_sum_not_one (h stages order_four)
theorem magnitude_interpretation_false : ¬(∀ ss : List Stage, OrderAtLeast 4 ss → negativeMagnitudeSum ss = 1) := by
  intro h; exact negative_magnitude_not_one (h stages order_four)
#print axioms order_four
#print axioms order_four_after_arbitrary_substitution
#print axioms conjecture6557_false
#print axioms magnitude_interpretation_false
end Conjecture6557
