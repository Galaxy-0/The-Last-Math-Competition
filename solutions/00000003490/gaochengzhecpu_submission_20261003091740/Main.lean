import Std

/-! A chromatic polynomial already determines the chromatic number.
Coloring counts below enumerate all actual vertex colorings. Equality of
polynomials is used only through equality of their natural evaluations. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Conjecture3490

def words (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (List.range k).flatMap (fun c => (words k n).map (c :: ·))

theorem words_nodup (k n : Nat) : (words k n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    change List.Pairwise (fun x y => x ≠ y) _
    rw [words, List.pairwise_flatMap]
    constructor
    · intro c hc
      rw [List.pairwise_map]
      apply List.Pairwise.imp _ ih
      intro x y hne heq
      exact hne (List.cons.inj heq).2
    · apply List.Pairwise.imp _ List.nodup_range
      intro c d hne x hx y hy heq
      rcases List.mem_map.mp hx with ⟨xs, hxs, rfl⟩
      rcases List.mem_map.mp hy with ⟨ys, hys, rfl⟩
      exact hne (List.cons.inj heq).1

theorem mem_words (k n : Nat) (cs : List Nat) :
    cs ∈ words k n ↔ cs.length = n ∧ ∀ c ∈ cs, c < k := by
  induction n generalizing cs with
  | zero =>
    simp only [words, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · intro h; subst cs; simp
    · intro h; exact h.1
  | succ n ih =>
    cases cs with
    | nil => simp [words]
    | cons c cs =>
      simp [words, List.mem_flatMap, List.mem_map, ih, and_assoc]
      constructor
      · rintro ⟨x, hx, l, hl, hb, rfl, rfl⟩
        exact ⟨hl, hx, hb⟩
      · rintro ⟨hl, hc, hb⟩
        exact ⟨c, hc, cs, hl, hb, rfl, rfl⟩

def Proper {n : Nat} (adj : Fin n → Fin n → Prop) (cs : List Nat) : Prop :=
  ∀ u v : Fin n, adj u v → cs[u.val]?.getD 0 ≠ cs[v.val]?.getD 0

instance {n : Nat} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (cs : List Nat) : Decidable (Proper adj cs) :=
  inferInstanceAs (Decidable (∀ u v : Fin n, adj u v → _ ≠ _))

def Colorable {n : Nat} (adj : Fin n → Fin n → Prop) (k : Nat) : Prop :=
  ∃ cs : List Nat, cs.length = n ∧ (∀ c ∈ cs, c < k) ∧ Proper adj cs

def chromaticEvaluation {n : Nat} (adj : Fin n → Fin n → Prop)
    [DecidableRel adj] (k : Nat) : Nat :=
  (words k n).countP (fun cs => decide (Proper adj cs))

theorem evaluation_pos_iff_colorable {n : Nat}
    (adj : Fin n → Fin n → Prop) [DecidableRel adj] (k : Nat) :
    0 < chromaticEvaluation adj k ↔ Colorable adj k := by
  unfold chromaticEvaluation
  rw [List.countP_pos_iff]
  constructor
  · rintro ⟨cs, hm, hp⟩
    have hw := (mem_words k n cs).mp hm
    exact ⟨cs, hw.1, hw.2, of_decide_eq_true hp⟩
  · rintro ⟨cs, hl, hb, hp⟩
    exact ⟨cs, (mem_words k n cs).mpr ⟨hl, hb⟩, decide_eq_true hp⟩

def ChromaticNumberIs {n : Nat} (adj : Fin n → Fin n → Prop) (r : Nat) : Prop :=
  Colorable adj r ∧ ∀ j, j < r → ¬Colorable adj j

def SameChromaticEvaluations {n m : Nat} (G : Fin n → Fin n → Prop)
    (H : Fin m → Fin m → Prop) [DecidableRel G] [DecidableRel H] : Prop :=
  ∀ k, chromaticEvaluation G k = chromaticEvaluation H k

theorem equal_evaluations_equal_chromatic_numbers {n m : Nat}
    (G : Fin n → Fin n → Prop) (H : Fin m → Fin m → Prop)
    [DecidableRel G] [DecidableRel H] (same : SameChromaticEvaluations G H)
    {g h : Nat} (hg : ChromaticNumberIs G g) (hh : ChromaticNumberIs H h) :
    g = h := by
  have transfer : ∀ k, Colorable G k ↔ Colorable H k := by
    intro k
    rw [←evaluation_pos_iff_colorable G k, ←evaluation_pos_iff_colorable H k, same k]
  have not_lt : ¬g < h := by
    intro lt
    exact hh.2 g lt ((transfer g).mp hg.1)
  have not_gt : ¬h < g := by
    intro lt
    exact hg.2 h lt ((transfer h).mpr hh.1)
  omega

/- The conjecture's pair-existence clause, with spectral equality dropped,
is WEAKER than the original claim. Even this weaker claim is impossible.
Same chromatic polynomials imply SameChromaticEvaluations by evaluation. -/
def SeparatingPairClaim : Prop :=
  ∃ n m : Nat, ∃ G : Fin n → Fin n → Prop, ∃ H : Fin m → Fin m → Prop,
  ∃ dg : DecidableRel G, ∃ dh : DecidableRel H, ∃ g h : Nat,
    @SameChromaticEvaluations n m G H dg dh ∧
    ChromaticNumberIs G g ∧ ChromaticNumberIs H h ∧ g ≠ h

theorem not_separating_pair_claim : ¬SeparatingPairClaim := by
  rintro ⟨n, m, G, H, dg, dh, g, h, same, hg, hh, different⟩
  exact different (@equal_evaluations_equal_chromatic_numbers n m G H dg dh same g h hg hh)

/- Integer coefficient lists, in ascending order, represent polynomials.
Trailing zero coefficients do not affect the argument. -/
def polynomialEval (p : List Int) (x : Int) : Int :=
  p.foldr (fun a y => a + x * y) 0

def IsChromaticPolynomial {n : Nat} (G : Fin n → Fin n → Prop)
    [DecidableRel G] (p : List Int) : Prop :=
  ∀ k : Nat, polynomialEval p (Int.ofNat k) = Int.ofNat (chromaticEvaluation G k)

def PolynomialSeparatingPairClaim : Prop :=
  ∃ n m : Nat, ∃ G : Fin n → Fin n → Prop, ∃ H : Fin m → Fin m → Prop,
  ∃ dg : DecidableRel G, ∃ dh : DecidableRel H, ∃ p : List Int, ∃ g h : Nat,
    @IsChromaticPolynomial n G dg p ∧ @IsChromaticPolynomial m H dh p ∧
    ChromaticNumberIs G g ∧ ChromaticNumberIs H h ∧ g ≠ h

theorem not_polynomial_separating_pair_claim : ¬PolynomialSeparatingPairClaim := by
  rintro ⟨n, m, G, H, dg, dh, p, g, h, hpG, hpH, hg, hh, different⟩
  have same : @SameChromaticEvaluations n m G H dg dh := by
    intro k
    exact Int.ofNat_inj.mp ((hpG k).symm.trans (hpH k))
  exact different (@equal_evaluations_equal_chromatic_numbers n m G H dg dh same g h hg hh)

#print axioms not_separating_pair_claim
#print axioms not_polynomial_separating_pair_claim
#print axioms evaluation_pos_iff_colorable
end Conjecture3490
