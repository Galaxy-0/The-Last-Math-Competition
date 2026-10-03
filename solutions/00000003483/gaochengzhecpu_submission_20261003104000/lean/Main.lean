import Std

/-! Counterexample to Conjecture 3483: a seven-vertex Hajós graph has
11 edges, attains 3e = 5v-2, is four-critical, but is not double-critical.
Double-critical means that deleting the two endpoints of every edge lowers
chromatic number by two.  All proper subgraphs are checked via single vertex
and edge deletions, with a symbolic restriction bridge. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Conjecture3483
abbrev V := Fin 7
abbrev Graph := List (Nat × Nat)
def Adj (G : Graph) (u v : V) : Prop :=
  (u.val, v.val) ∈ G ∨ (v.val, u.val) ∈ G
instance (G : Graph) (u v : V) : Decidable (Adj G u v) := inferInstanceAs (Decidable (_ ∨ _))
def tuple {k : Nat} (c0 c1 c2 c3 c4 c5 c6 : Fin k) (v : V) : Fin k :=
  match v.val with
  | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | 5 => c5 | _ => c6
theorem tuple_eta {k : Nat} (c : V → Fin k) :
    tuple (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) = c := by
  funext v
  have h : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by
    have hv : v.val < 7 := v.isLt
    simp only [Fin.ext_iff]
    omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
def Proper {k : Nat} (G : Graph) (c : V → Fin k) : Prop :=
  ∀ u v, Adj G u v → c u ≠ c v
def ProperDeleted {k : Nat} (G : Graph) (x : V) (c : V → Fin k) : Prop :=
  ∀ u v, u ≠ x → v ≠ x → Adj G u v → c u ≠ c v
def ProperEdgeDeleted {k : Nat} (G : Graph) (a b : V) (c : V → Fin k) : Prop :=
  ∀ u v, Adj G u v → ¬((u = a ∧ v = b) ∨ (u = b ∧ v = a)) → c u ≠ c v
instance {k : Nat} (G : Graph) (c : V → Fin k) : Decidable (Proper G c) :=
  inferInstanceAs (Decidable (∀ u v, Adj G u v → c u ≠ c v))
instance {k : Nat} (G : Graph) (x : V) (c : V → Fin k) : Decidable (ProperDeleted G x c) :=
  inferInstanceAs (Decidable (∀ u v, u ≠ x → v ≠ x → Adj G u v → c u ≠ c v))
instance {k : Nat} (G : Graph) (a b : V) (c : V → Fin k) : Decidable (ProperEdgeDeleted G a b c) :=
  inferInstanceAs (Decidable (∀ u v, Adj G u v → ¬((u = a ∧ v = b) ∨ (u = b ∧ v = a)) → c u ≠ c v))
def G : Graph := [(0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (2, 3), (4, 5), (4, 6), (5, 6)]
def Gfour : V → Fin 4 := tuple 0 0 1 2 1 2 3
def Gvertex (x : V) : V → Fin 3 :=
  if x = 0 then tuple 0 0 1 2 1 0 2 else
  if x = 1 then tuple 0 0 1 2 0 1 2 else
  if x = 2 then tuple 0 1 0 2 0 1 2 else
  if x = 3 then tuple 0 1 2 0 0 1 2 else
  if x = 4 then tuple 0 0 1 2 0 1 2 else
  if x = 5 then tuple 0 0 1 2 1 0 2 else
  tuple 0 0 1 2 1 2 0
def Gedge (a b : V) : V → Fin 3 :=
  if (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) then tuple 0 1 0 2 0 1 2 else
  if (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) then tuple 0 1 2 0 0 1 2 else
  if (a = 0 ∧ b = 5) ∨ (a = 5 ∧ b = 0) then tuple 0 0 1 2 1 0 2 else
  if (a = 0 ∧ b = 6) ∨ (a = 6 ∧ b = 0) then tuple 0 0 1 2 1 2 0 else
  if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then tuple 0 1 1 2 0 1 2 else
  if (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then tuple 0 1 2 1 0 1 2 else
  if (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) then tuple 0 0 1 2 0 1 2 else
  if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then tuple 0 1 2 2 0 1 2 else
  if (a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4) then tuple 0 0 1 2 1 1 2 else
  if (a = 4 ∧ b = 6) ∨ (a = 6 ∧ b = 4) then tuple 0 0 1 2 1 2 1 else
  if (a = 5 ∧ b = 6) ∨ (a = 6 ∧ b = 5) then tuple 0 0 1 2 1 2 2 else
  tuple 0 0 0 0 0 0 0
theorem G_four : Proper G Gfour := by decide
theorem G_no_three_tuple : ∀ a b c d e f g : Fin 3, ¬Proper G (tuple a b c d e f g) := by decide
theorem G_no_three (c : V → Fin 3) : ¬Proper G c := by
  have h := G_no_three_tuple (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)
  rw [tuple_eta] at h
  exact h
theorem G_vertex_three : ∀ x : V, ProperDeleted G x (Gvertex x) := by decide
theorem G_edge_three : ∀ a b : V, Adj G a b → ProperEdgeDeleted G a b (Gedge a b) := by decide
theorem G_vertex_no_two_tuple : ∀ x : V, ∀ a b c d e f g : Fin 2, ¬ProperDeleted G x (tuple a b c d e f g) := by decide
theorem G_vertex_no_two (x : V) (c : V → Fin 2) : ¬ProperDeleted G x c := by
  have h := G_vertex_no_two_tuple x (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)
  rw [tuple_eta] at h
  exact h
/- Strong criticality: all proper subgraphs, including vertex and edge
deletions, admit three colors. Subgraphs are encoded on subsets of V;
colorings of their vertex subsets extend arbitrarily to V. -/
def AllProperSubgraphsThree (K : Graph) : Prop :=
  ∀ present : V → Prop, ∀ A : V → V → Prop,
    (∀ u v, A u v ↔ A v u) →
    (∀ u v, A u v → present u ∧ present v ∧ Adj K u v) →
    ((∃ x, ¬present x) ∨ ∃ a b, Adj K a b ∧ ¬A a b) →
    ∃ c : V → Fin 3, ∀ u v, A u v → c u ≠ c v

theorem proper_subgraph_bridge (K : Graph)
    (vertex : ∀ x : V, ∃ c : V → Fin 3, ProperDeleted K x c)
    (edge : ∀ a b : V, Adj K a b → ∃ c : V → Fin 3, ProperEdgeDeleted K a b c) :
    AllProperSubgraphsThree K := by
  intro present A sym sub proper
  rcases proper with missing | missing
  · rcases missing with ⟨x, hx⟩
    rcases vertex x with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro u v huv
    have hs := sub u v huv
    have hu : u ≠ x := by intro h; subst u; exact hx hs.1
    have hv : v ≠ x := by intro h; subst v; exact hx hs.2.1
    exact hc u v hu hv hs.2.2
  · rcases missing with ⟨a, b, hab, hn⟩
    rcases edge a b hab with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro u v huv
    apply hc u v (sub u v huv).2.2
    intro forbidden
    rcases forbidden with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hn huv
    · exact hn ((sym _ _).mp huv)

def ChromaticNumberIs (K : Graph) (r : Nat) : Prop :=
  (∃ c : V → Fin r, Proper K c) ∧
    ∀ k, k < r → ¬∃ c : V → Fin k, Proper K c

theorem chromatic_four (K : Graph) (c4 : V → Fin 4) (hc4 : Proper K c4)
    (hn : ∀ c : V → Fin 3, ¬Proper K c) : ChromaticNumberIs K 4 := by
  refine ⟨⟨c4, hc4⟩, ?_⟩
  intro k hk h
  rcases h with ⟨c, hc⟩
  let c3 : V → Fin 3 := fun v => ⟨(c v).val, by have ht := (c v).isLt; omega⟩
  apply hn c3
  intro u v huv heq
  apply hc u v huv
  apply Fin.ext
  exact congrArg (fun z : Fin 3 => z.val) heq

def FourCritical (K : Graph) : Prop := ChromaticNumberIs K 4 ∧ AllProperSubgraphsThree K

theorem G_four_critical : FourCritical G := by
  refine ⟨chromatic_four G Gfour G_four G_no_three, ?_⟩
  apply proper_subgraph_bridge
  · intro x; exact ⟨Gvertex x, G_vertex_three x⟩
  · intro a b hab; exact ⟨Gedge a b, G_edge_three a b hab⟩


/-- Removing both a and b, while retaining their unused labels in the ambient carrier. -/
def ProperPairDeleted {k : Nat} (K : Graph) (a b : V) (c : V → Fin k) : Prop :=
  ∀ u v, u ≠ a → u ≠ b → v ≠ a → v ≠ b → Adj K u v → c u ≠ c v

def PairDeletionChromaticNumberIs (K : Graph) (a b : V) (r : Nat) : Prop :=
  (∃ c : V → Fin r, ProperPairDeleted K a b c) ∧
    ∀ k, k < r → ¬ ∃ c : V → Fin k, ProperPairDeleted K a b c

inductive Reach (K : Graph) : V → V → Prop where
  | refl (v : V) : Reach K v v
  | step {u v w : V} : Adj K u v → Reach K v w → Reach K u w

def Connected (K : Graph) : Prop := ∀ u v, Reach K u v

/-- Standard double-criticality, specialized to four-chromatic graphs. -/
def DoubleCriticalFour (K : Graph) : Prop :=
  Connected K ∧ ChromaticNumberIs K 4 ∧
    ∀ a b, Adj K a b → PairDeletionChromaticNumberIs K a b 2

/-- Each unordered edge occurs once, in increasing endpoint order, inside V. -/
def NormalizedSimple (K : Graph) : Prop :=
  K.Nodup ∧ ∀ e ∈ K, e.1 < e.2 ∧ e.2 < 7

theorem G_normalized_simple : NormalizedSimple G := by
  unfold NormalizedSimple
  decide

theorem G_vertex_count : (List.finRange 7).length = 7 := by decide
theorem G_edge_count : G.length = 11 := by decide
theorem G_attains_equality : 3 * G.length = 5 * 7 - 2 := by decide

-- Deleting endpoints 0 and 2 of the edge {0,2} leaves the triangle {4,5,6}.
theorem G_witness_edge : Adj G 0 2 := by decide
theorem G_surviving_triangle :
    Adj G 4 5 ∧ Adj G 5 6 ∧ Adj G 4 6 ∧
    (4 : V) ≠ 0 ∧ (4 : V) ≠ 2 ∧
    (5 : V) ≠ 0 ∧ (5 : V) ≠ 2 ∧
    (6 : V) ≠ 0 ∧ (6 : V) ≠ 2 := by decide

theorem three_colors_not_pairwise_distinct (a b c : Fin 2) :
    ¬ (a ≠ b ∧ b ≠ c ∧ a ≠ c) := by
  have finite_check : ∀ a b c : Fin 2, ¬ (a ≠ b ∧ b ≠ c ∧ a ≠ c) := by decide
  exact finite_check a b c

theorem G_pair_not_two (c : V → Fin 2) : ¬ ProperPairDeleted G 0 2 c := by
  intro hc
  have h45 := hc 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h56 := hc 5 6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h46 := hc 4 6 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact three_colors_not_pairwise_distinct (c 4) (c 5) (c 6) ⟨h45, h56, h46⟩

theorem G_pair_three : ProperPairDeleted G 0 2 (Gvertex 0) := by
  intro u v hu _ hv _ huv
  exact G_vertex_three 0 u v hu hv huv

theorem G_pair_chromatic_three : PairDeletionChromaticNumberIs G 0 2 3 := by
  refine ⟨⟨Gvertex 0, G_pair_three⟩, ?_⟩
  intro k hk h
  rcases h with ⟨c, hc⟩
  let c2 : V → Fin 2 := fun v => ⟨(c v).val, by have ht := (c v).isLt; omega⟩
  apply G_pair_not_two c2
  intro u v hua hub hva hvb huv heq
  apply hc u v hua hub hva hvb huv
  exact Fin.ext (congrArg (fun z : Fin 2 => z.val) heq)

theorem G_not_double_critical : ¬ DoubleCriticalFour G := by
  intro h
  rcases (h.2.2 0 2 G_witness_edge).1 with ⟨c, hc⟩
  exact G_pair_not_two c hc

/-- A necessary seven-vertex specialization of the equality-only assertion.
Any extra "nearly-four-regular" requirement can only strengthen its conclusion. -/
def EqualityForcesDoubleCritical : Prop :=
  ∀ K : Graph, NormalizedSimple K → FourCritical K →
    3 * K.length = 5 * 7 - 2 → DoubleCriticalFour K

theorem conjecture3483_counterexample : ¬ EqualityForcesDoubleCritical := by
  intro h
  exact G_not_double_critical (h G G_normalized_simple G_four_critical G_attains_equality)

theorem full_conjecture_false (OtherAssertions : Prop) :
    ¬ (EqualityForcesDoubleCritical ∧ OtherAssertions) := by
  intro h
  exact conjecture3483_counterexample h.1

#print axioms G_normalized_simple
#print axioms G_four_critical
#print axioms G_attains_equality
#print axioms G_pair_chromatic_three
#print axioms G_not_double_critical
#print axioms conjecture3483_counterexample
#print axioms full_conjecture_false

end Conjecture3483
