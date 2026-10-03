import Std
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace Conjecture3486
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
def H : Graph := [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 6), (4, 6), (5, 6)]
def Hfour : V → Fin 4 := tuple 0 1 2 0 1 2 3
def Hvertex (x : V) : V → Fin 3 :=
  if x = 0 then tuple 0 0 1 2 0 2 1 else
  if x = 1 then tuple 0 0 1 0 2 2 1 else
  if x = 2 then tuple 0 1 0 0 2 2 1 else
  if x = 3 then tuple 0 1 2 0 1 2 0 else
  if x = 4 then tuple 0 1 2 0 0 2 1 else
  if x = 5 then tuple 0 1 2 0 1 0 2 else
  tuple 0 1 2 0 1 2 0
def Hedge (a b : V) : V → Fin 3 :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then tuple 0 0 1 2 2 1 0 else
  if (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) then tuple 0 1 0 2 1 2 0 else
  if (a = 0 ∧ b = 4) ∨ (a = 4 ∧ b = 0) then tuple 0 1 2 0 0 2 1 else
  if (a = 0 ∧ b = 5) ∨ (a = 5 ∧ b = 0) then tuple 0 1 2 0 1 0 2 else
  if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then tuple 0 1 1 0 2 2 1 else
  if (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) then tuple 0 1 2 1 1 2 0 else
  if (a = 1 ∧ b = 5) ∨ (a = 5 ∧ b = 1) then tuple 0 1 2 0 1 1 2 else
  if (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then tuple 0 1 2 2 1 2 0 else
  if (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) then tuple 0 1 2 0 2 2 1 else
  if (a = 3 ∧ b = 6) ∨ (a = 6 ∧ b = 3) then tuple 0 1 2 0 1 2 0 else
  if (a = 4 ∧ b = 6) ∨ (a = 6 ∧ b = 4) then tuple 0 1 2 0 1 2 1 else
  if (a = 5 ∧ b = 6) ∨ (a = 6 ∧ b = 5) then tuple 0 1 2 0 1 2 2 else
  tuple 0 0 0 0 0 0 0
theorem H_four : Proper H Hfour := by decide
theorem H_no_three_tuple : ∀ a b c d e f g : Fin 3, ¬Proper H (tuple a b c d e f g) := by decide
theorem H_no_three (c : V → Fin 3) : ¬Proper H c := by
  have h := H_no_three_tuple (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)
  rw [tuple_eta] at h
  exact h
theorem H_vertex_three : ∀ x : V, ProperDeleted H x (Hvertex x) := by decide
theorem H_edge_three : ∀ a b : V, Adj H a b → ProperEdgeDeleted H a b (Hedge a b) := by decide
theorem H_vertex_no_two_tuple : ∀ x : V, ∀ a b c d e f g : Fin 2, ¬ProperDeleted H x (tuple a b c d e f g) := by decide
theorem H_vertex_no_two (x : V) (c : V → Fin 2) : ¬ProperDeleted H x c := by
  have h := H_vertex_no_two_tuple x (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)
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

theorem H_four_critical : FourCritical H := by
  refine ⟨chromatic_four H Hfour H_four H_no_three, ?_⟩
  apply proper_subgraph_bridge
  · intro x; exact ⟨Hvertex x, H_vertex_three x⟩
  · intro a b hab; exact ⟨Hedge a b, H_edge_three a b hab⟩

def DeletionChromaticNumberIs (K : Graph) (x : V) (r : Nat) : Prop :=
  (∃ c : V → Fin r, ProperDeleted K x c) ∧
    ∀ k, k < r → ¬∃ c : V → Fin k, ProperDeleted K x c

theorem deletion_chromatic_three (K : Graph) (x : V)
    (c3 : V → Fin 3) (hc3 : ProperDeleted K x c3)
    (hn : ∀ c : V → Fin 2, ¬ProperDeleted K x c) :
    DeletionChromaticNumberIs K x 3 := by
  refine ⟨⟨c3, hc3⟩, ?_⟩
  intro k hk h
  rcases h with ⟨c, hc⟩
  let c2 : V → Fin 2 := fun v => ⟨(c v).val, by have ht := (c v).isLt; omega⟩
  apply hn c2
  intro u v hu hv huv heq
  apply hc u v hu hv huv
  apply Fin.ext
  exact congrArg (fun z : Fin 2 => z.val) heq

theorem same_deletion_spectrum : ∀ x : V,
    DeletionChromaticNumberIs G x 3 ∧ DeletionChromaticNumberIs H x 3 := by
  intro x
  exact ⟨deletion_chromatic_three G x (Gvertex x) (G_vertex_three x) (G_vertex_no_two x),
    deletion_chromatic_three H x (Hvertex x) (H_vertex_three x) (H_vertex_no_two x)⟩

def Triangle (K : Graph) (a b c : V) : Prop := Adj K a b ∧ Adj K b c ∧ Adj K c a
instance (K : Graph) (a b c : V) : Decidable (Triangle K a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem H_no_disjoint_triangles : ∀ a b c d e f : V,
    ¬([a,b,c,d,e,f].Nodup ∧ Triangle H a b c ∧ Triangle H d e f) := by decide

def Isomorphic (K L : Graph) : Prop :=
  ∃ f : V → V, (∀ u v, f u = f v → u = v) ∧
    (∀ y, ∃ x, f x = y) ∧ (∀ u v, Adj K u v ↔ Adj L (f u) (f v))

theorem graphs_not_isomorphic : ¬Isomorphic G H := by
  rintro ⟨f, inj, surj, adj⟩
  have hd : [f 1, f 2, f 3, f 4, f 5, f 6].Nodup := by
    change List.Pairwise (fun x y => x ≠ y) (List.map f [1,2,3,4,5,6])
    rw [List.pairwise_map]
    apply List.Pairwise.imp _ (by decide : ([1,2,3,4,5,6] : List V).Nodup)
    intro x y hne heq
    exact hne (inj x y heq)
  have ht1 : Triangle H (f 1) (f 2) (f 3) :=
    ⟨(adj 1 2).mp (by decide), (adj 2 3).mp (by decide), (adj 3 1).mp (by decide)⟩
  have ht2 : Triangle H (f 4) (f 5) (f 6) :=
    ⟨(adj 4 5).mp (by decide), (adj 5 6).mp (by decide), (adj 6 4).mp (by decide)⟩
  exact H_no_disjoint_triangles (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) ⟨hd, ht1, ht2⟩

theorem graphs_simple :
    (∀ x : V, ¬Adj G x x ∧ ¬Adj H x x) ∧
    (∀ x y : V, (Adj G x y ↔ Adj G y x) ∧ (Adj H x y ↔ Adj H y x)) := by decide

/- Minimum order 13 would prohibit any such pair at order 7. -/
def NoSevenVertexPairClaim : Prop := ∀ K L : Graph,
  FourCritical K → FourCritical L →
  (∀ x : V, DeletionChromaticNumberIs K x 3 ∧ DeletionChromaticNumberIs L x 3) →
  Isomorphic K L

theorem not_minimum_thirteen_consequence : ¬NoSevenVertexPairClaim := by
  intro h
  exact graphs_not_isomorphic (h G H G_four_critical H_four_critical same_deletion_spectrum)

theorem counterexample_order_less_than_thirteen : 7 < 13 := by decide

#print axioms not_minimum_thirteen_consequence
#print axioms G_four_critical
#print axioms H_four_critical
#print axioms same_deletion_spectrum
#print axioms graphs_not_isomorphic
end Conjecture3486
