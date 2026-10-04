import Std
namespace Submission

theorem nodup_subset_length {α : Type} [BEq α] [LawfulBEq α]
    (xs ys : List α) (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    have hay : a ∈ ys := hs (by simp)
    have sub : xs ⊆ ys.erase a := by
      intro b hb
      apply (List.mem_erase_of_ne (show b ≠ a from fun h => ha (h ▸ hb))).mpr
      exact hs (by simp [hb])
    have h := ih (ys.erase a) ht sub
    have pos := List.length_pos_of_mem hay
    rw [List.length_erase_of_mem hay] at h
    simp only [List.length_cons]
    omega

def vertices (m : List (Nat × Nat)) : List Nat := m.flatMap (fun e => [e.1, e.2])

theorem vertices_length (m : List (Nat × Nat)) : (vertices m).length = 2 * m.length := by
  induction m with
  | nil => simp [vertices]
  | cons e m ih =>
    have step : vertices (e :: m) = [e.1, e.2] ++ vertices m := rfl
    rw [step]
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [ih]
    omega

structure Graph where
  order : Nat
  adjacent : Nat → Nat → Prop
  symmetric : ∀ a b, adjacent a b → adjacent b a
  irreflexive : ∀ a, ¬ adjacent a a

structure Matching (g : Graph) where
  edges : List (Nat × Nat)
  canonical : ∀ e ∈ edges, e.1 < e.2
  graphEdges : ∀ e ∈ edges, g.adjacent e.1 e.2
  disjoint : (vertices edges).Nodup
  bounded : ∀ v ∈ vertices edges, v < g.order

theorem matching_bound {g : Graph} (m : Matching g) : 2 * m.edges.length ≤ g.order := by
  have sub : vertices m.edges ⊆ List.range g.order := by
    intro v hv
    exact List.mem_range.mpr (m.bounded v hv)
  have h := nodup_subset_length (vertices m.edges) (List.range g.order) m.disjoint sub
  simpa [vertices_length] using h

def removeEdges (m r : List (Nat × Nat)) : List (Nat × Nat) :=
  r.foldl List.erase m

theorem remove_length (m r : List (Nat × Nat)) (hr : r.Nodup) (hsub : r ⊆ m) :
    (removeEdges m r).length + r.length = m.length := by
  induction r generalizing m with
  | nil => simp [removeEdges]
  | cons a r ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hr
    have ham : a ∈ m := hsub (by simp)
    have hs : r ⊆ m.erase a := by
      intro b hb
      apply (List.mem_erase_of_ne (show b ≠ a from fun h => ha (h ▸ hb))).mpr
      exact hsub (by simp [hb])
    have h := ih (m.erase a) hn hs
    have pos := List.length_pos_of_mem ham
    rw [List.length_erase_of_mem ham] at h
    simp only [removeEdges, List.foldl_cons, List.length_cons]
    change (removeEdges (m.erase a) r).length + (r.length + 1) = m.length
    omega





def edge (a b : Nat) : Nat × Nat := (min a b, max a b)

def freeEdges : List Nat → List (Nat × Nat)
  | a :: b :: c :: rest => edge a b :: freeEdges (c :: rest)
  | [a,b] => [edge a b]
  | _ => []

def matchedEdges : List Nat → List (Nat × Nat)
  | _ :: b :: c :: rest => edge b c :: matchedEdges (c :: rest)
  | _ => []

theorem alternating_balance (p : List Nat) (he : p.length % 2 = 0)
    (hl : 2 ≤ p.length) : (freeEdges p).length = (matchedEdges p).length + 1 := by
  match p with
  | [] => simp at hl
  | [a] => simp at hl
  | [a,b] => rfl
  | [a,b,c] => simp at he
  | a :: b :: c :: d :: rest =>
    have ht : (c :: d :: rest).length % 2 = 0 := by simp only [List.length_cons] at *; omega
    have hh := alternating_balance (c :: d :: rest) ht (by simp)
    change (freeEdges (c :: d :: rest)).length + 1 = (matchedEdges (c :: d :: rest)).length + 1 + 1
    omega
termination_by p.length

def toggle (m : List (Nat × Nat)) (p : List Nat) : List (Nat × Nat) :=
  removeEdges m (matchedEdges p) ++ freeEdges p

structure AugmentingPath {g : Graph} (m : Matching g) where
  nodes : List Nat
  simple : nodes.Nodup
  nontrivial : 2 ≤ nodes.length
  evenNodes : nodes.length % 2 = 0
  bounded : ∀ v ∈ nodes, v < g.order
  edgesInGraph : ∀ e ∈ freeEdges nodes ++ matchedEdges nodes, g.adjacent e.1 e.2
  alternatingFree : ∀ e ∈ freeEdges nodes, e ∉ m.edges
  alternatingMatched : matchedEdges nodes ⊆ m.edges
  noRepeatedMatchedEdges : (matchedEdges nodes).Nodup
  startFree : ∀ v, edge nodes.head! v ∉ m.edges
  endFree : ∀ v, edge nodes.getLast! v ∉ m.edges

theorem augmentation_size {g : Graph} (m : Matching g) (p : AugmentingPath m) :
    (toggle m.edges p.nodes).length = m.edges.length + 1 := by
  have hr := remove_length m.edges (matchedEdges p.nodes)
    p.noRepeatedMatchedEdges p.alternatingMatched
  have hb := alternating_balance p.nodes p.evenNodes p.nontrivial
  simp only [toggle, List.length_append]
  omega

/-- A run records each matching and the actual alternating path used to obtain the next one. -/
inductive Run {g : Graph} : Matching g → Matching g → Nat → Prop
  | stop (m) : Run m m 0
  | step {initial next final k} (path : AugmentingPath initial)
      (update : next.edges = toggle initial.edges path.nodes)
      (tail : Run next final k) : Run initial final (k+1)

theorem run_size {g : Graph} {initial final : Matching g} {k : Nat}
    (h : Run initial final k) : final.edges.length = initial.edges.length + k := by
  induction h with
  | stop m => simp
  | @step initial next final k path update tail ih =>
    have hs := augmentation_size initial path
    rw [← update] at hs
    omega

theorem run_bound {g : Graph} {initial final : Matching g} {k : Nat}
    (h : Run initial final k) : 2 * k ≤ g.order := by
  have hs := run_size h
  have hb := matching_bound final
  omega

/-- The lower half of the asserted Theta(n^2 log n) law, with an integer reciprocal
constant and floor(log_2 n). This is equivalent in asymptotic scale to any fixed log base. -/
def ClaimedLowerBound : Prop :=
  ∃ c N : Nat, 0 < c ∧ ∀ n : Nat, N ≤ n →
    ∃ g : Graph, g.order = n ∧ ∃ initial final : Matching g, ∃ k : Nat,
      Run initial final k ∧ n*n*Nat.log2 n ≤ c*k

theorem conjecture_00000003943_false : ¬ ClaimedLowerBound := by
  rintro ⟨c,N,hc,hl⟩
  let n := c + N + 2
  obtain ⟨g,horder,initial,final,k,hr,hgrowth⟩ := hl n (by omega)
  have hk : k ≤ n := by have := run_bound hr; omega
  have hn : 0 < n := by omega
  have hcn : c < n := by omega
  have hlog : 1 ≤ Nat.log2 n := by
    rw [Nat.log2]
    simp only [if_pos (show n ≥ 2 by omega)]
    omega
  have hquad : n*n ≤ n*n*Nat.log2 n := Nat.le_mul_of_pos_right (n*n) (by omega)
  have hck : c*k ≤ c*n := Nat.mul_le_mul_left c hk
  have hstrict : c*n < n*n := Nat.mul_lt_mul_of_pos_right hcn hn
  omega

#print axioms matching_bound
#print axioms augmentation_size
#print axioms run_bound
#print axioms conjecture_00000003943_false
end Submission
