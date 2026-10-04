import Mathlib.SetTheory.Game.Short
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic.DeriveCountable

noncomputable section
namespace ShortGames8873
open SetTheory
open scoped PGame Cardinal

inductive Code
  | nil : Code
  | cons : Code → Code → Code
  | node : Code → Code → Code
  deriving Countable

mutual
  def decode : Code → PGame.{0}
    | .node l r => PGame.ofLists (decodeOptions l) (decodeOptions r)
    | _ => 0
  def decodeOptions : Code → List PGame.{0}
    | .cons x xs => decode x :: decodeOptions xs
    | _ => []
end

def encodeOptions : List Code → Code
  | [] => .nil
  | x :: xs => .cons x (encodeOptions xs)

theorem decode_encode_options (cs : List Code) :
    decodeOptions (encodeOptions cs) = cs.map decode := by
  induction cs with
  | nil => rfl
  | cons x xs ih => simp [encodeOptions, decodeOptions, ih]

theorem represents_every_short (x : PGame.{0}) (s : PGame.Short x) :
    ∃ c : Code, Nonempty (PGame.Relabelling x (decode c)) := by
  classical
  induction s with
  | @mk α β L R sL sR instL instR ihL ihR =>
    let cl : α → Code := fun i => (ihL i).choose
    let cr : β → Code := fun i => (ihR i).choose
    let el := Fintype.equivFin α
    let er := Fintype.equivFin β
    let ls := List.ofFn (fun i => cl (el.symm i))
    let rs := List.ofFn (fun i => cr (er.symm i))
    refine ⟨Code.node (encodeOptions ls) (encodeOptions rs), ⟨?_⟩⟩
    simp only [decode, decode_encode_options]
    refine PGame.Relabelling.mk
      ((el.trans (finCongr (by simp [ls]))).trans Equiv.ulift.symm)
      ((er.trans (finCongr (by simp [rs]))).trans Equiv.ulift.symm) ?_ ?_
    · intro i
      simpa [PGame.ofLists, ls, cl, el] using (ihL i).choose_spec.some
    · intro i
      simpa [PGame.ofLists, rs, cr, er] using (ihR i).choose_spec.some

theorem decoded_short_and_options (c : Code) :
    Nonempty (PGame.Short (decode c)) ∧ Nonempty (PGame.ListShort (decodeOptions c)) := by
  induction c with
  | nil =>
    simp only [decode, decodeOptions]
    exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩
  | cons x xs ihx ihxs =>
    simp only [decode, decodeOptions]
    letI : PGame.Short (decode x) := ihx.1.some
    letI : PGame.ListShort (decodeOptions xs) := ihxs.2.some
    exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩
  | node l r ihl ihr =>
    simp only [decode, decodeOptions]
    letI : PGame.ListShort (decodeOptions l) := ihl.2.some
    letI : PGame.ListShort (decodeOptions r) := ihr.2.some
    exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

def IsShortValue (v : Game.{0}) : Prop :=
  ∃ x : PGame.{0}, Nonempty (PGame.Short x) ∧ (⟦x⟧ : Game) = v
abbrev ShortValue := {v : Game.{0} // IsShortValue v}

def value (c : Code) : ShortValue :=
  ⟨⟦decode c⟧, decode c, (decoded_short_and_options c).1, rfl⟩

theorem value_surjective : Function.Surjective value := by
  intro v
  obtain ⟨x, hx, he⟩ := v.property
  obtain ⟨c, hc⟩ := represents_every_short x hx.some
  refine ⟨c, Subtype.ext ?_⟩
  change (⟦decode c⟧ : Game) = v.val
  rw [← he]
  exact (PGame.game_eq hc.some.equiv).symm

instance short_values_countable : Countable ShortValue :=
  value_surjective.countable

theorem short_value_cardinal_lt_continuum :
    Cardinal.mk ShortValue < Cardinal.continuum :=
  Cardinal.mk_le_aleph0.trans_lt Cardinal.aleph0_lt_continuum

theorem conjecture_8873_false :
    Cardinal.mk ShortValue ≠ Cardinal.continuum :=
  ne_of_lt short_value_cardinal_lt_continuum

end ShortGames8873
#print axioms ShortGames8873.instCountableCode
#print axioms ShortGames8873.represents_every_short
#print axioms ShortGames8873.value_surjective
#print axioms ShortGames8873.conjecture_8873_false
