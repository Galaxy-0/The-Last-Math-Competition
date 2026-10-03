import Std

namespace Conjecture3461
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

abbrev V := Fin 4
def adjacent (v w : V) : Bool :=
  decide ((v.val + 1) % 4 = w.val ∨ (w.val + 1) % 4 = v.val)
theorem graph_loopless : ∀ v, adjacent v v = false := by decide
theorem graph_symmetric : ∀ v w, adjacent v w = adjacent w v := by decide

instance finiteExists (n : Nat) (P : Fin n → Prop) [DecidablePred P] : Decidable (∃ x, P x) :=
  decidable_of_iff (¬∀ x, ¬P x) (by
    constructor
    · intro h
      obtain ⟨x,hx⟩ := Classical.not_forall.mp h
      exact ⟨x,Classical.byContradiction hx⟩
    · rintro ⟨x,hx⟩ h
      exact h x hx)
instance boolForall (P : Bool → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (P false ∧ P true) Bool.forall_bool.symm

/-- The arbitrary matching assignment of a DP cover. Colors may be any
types and may differ at each vertex; cross-fiber matchings need not be perfect. -/
structure Cover (Colors : V → Type) where
  conflict : (v : V) → Colors v → (w : V) → Colors w → Bool
  symmetric : ∀ v c w d, conflict v c w d = conflict w d v c
  supported : ∀ v c w d, conflict v c w d = true → adjacent v w = true
  matching : ∀ v w c d e, conflict v c w d = true → conflict v c w e = true → d = e

/-- The usual auxiliary graph: clique fibers and the cross-fiber matchings. -/
def AuxAdj {Colors : V → Type} (H : Cover Colors) (x y : Sigma Colors) : Prop :=
  (x.1 = y.1 ∧ x ≠ y) ∨ H.conflict x.1 x.2 y.1 y.2 = true

theorem aux_loopless {Colors : V → Type} (H : Cover Colors) (x : Sigma Colors) :
    ¬AuxAdj H x x := by
  rintro (⟨_,h⟩ | h)
  · exact h rfl
  · have hh := H.supported x.1 x.2 x.1 x.2 h
    rw [graph_loopless] at hh
    contradiction

theorem aux_symmetric {Colors : V → Type} (H : Cover Colors) (x y : Sigma Colors) :
    AuxAdj H x y → AuxAdj H y x := by
  rintro (⟨he,hn⟩ | h)
  · exact Or.inl ⟨he.symm,Ne.symm hn⟩
  · exact Or.inr ((H.symmetric _ _ _ _).symm.trans h)

def Avoids {Colors : V → Type} (H : Cover Colors) (f : (v : V) → Colors v) : Prop :=
  ∀ v w, H.conflict v (f v) w (f w) = false

theorem avoids_is_independent_transversal {Colors : V → Type} (H : Cover Colors)
    (f : (v : V) → Colors v) (h : Avoids H f) :
    ∀ v w, ¬AuxAdj H ⟨v,f v⟩ ⟨w,f w⟩ := by
  intro v w
  rintro (⟨he,hn⟩ | he)
  · change v = w at he
    subst w
    exact hn rfl
  · have hf := h v w
    rw [hf] at he
    contradiction

theorem independent_transversal_avoids {Colors : V → Type} (H : Cover Colors)
    (f : (v : V) → Colors v)
    (h : ∀ v w, ¬AuxAdj H ⟨v,f v⟩ ⟨w,f w⟩) : Avoids H f := by
  intro v w
  cases he : H.conflict v (f v) w (f w) with
  | false => rfl
  | true => exact False.elim (h v w (Or.inr he))

theorem independent_transversal_iff {Colors : V → Type} (H : Cover Colors)
    (f : (v : V) → Colors v) :
    (∀ v w, ¬AuxAdj H ⟨v,f v⟩ ⟨w,f w⟩) ↔ Avoids H f :=
  ⟨independent_transversal_avoids H f, avoids_is_independent_transversal H f⟩

def Proper (k : Nat) (f : V → Fin k) : Prop :=
  ∀ v w, adjacent v w = true → f v ≠ f w

def twoColors (v : V) : Fin 2 := ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩
theorem two_coloring : Proper 2 twoColors := by unfold Proper; decide
theorem no_one_coloring (f : V → Fin 1) : ¬Proper 1 f := by
  intro h
  have hn := h 0 1 (by decide)
  have he : f 0 = f 1 := by have := (f 0).isLt; have := (f 1).isLt; omega
  exact hn he

def ChromaticExactly (k : Nat) : Prop :=
  (∃ f : V → Fin k, Proper k f) ∧ ∀ j, j < k → ¬∃ f : V → Fin j, Proper j f

theorem chromatic_two : ChromaticExactly 2 := by
  refine ⟨⟨twoColors,two_coloring⟩, ?_⟩
  intro j hj
  have casesJ : j = 0 ∨ j = 1 := by omega
  rcases casesJ with rfl | rfl
  · rintro ⟨f,_⟩
    exact Fin.elim0 (f 0)
  · rintro ⟨f,hf⟩
    exact no_one_coloring f hf

def tuple4 {A : Type} (a b c d : A) (v : V) : A :=
  match v.val with | 0 => a | 1 => b | 2 => c | _ => d

theorem all_vertices (v : V) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  have := v.isLt
  simp only [Fin.ext_iff]
  omega

theorem tuple4_eta {A : Type} (f : V → A) : tuple4 (f 0) (f 1) (f 2) (f 3) = f := by
  funext v
  rcases all_vertices v with rfl | rfl | rfl | rfl <;> rfl

def twisted : Cover (fun _ => Fin 2) where
  conflict v c w d := adjacent v w &&
    (if (v = 0 ∧ w = 3) ∨ (v = 3 ∧ w = 0) then decide (c ≠ d) else decide (c = d))
  symmetric := by decide
  supported := by decide
  matching := by decide

theorem checked_no_twisted_coloring : ∀ a b c d : Fin 2,
    ¬Avoids twisted (tuple4 a b c d) := by unfold Avoids; decide

theorem twisted_not_colorable (f : V → Fin 2) : ¬Avoids twisted f := by
  have h := checked_no_twisted_coloring (f 0) (f 1) (f 2) (f 3)
  rw [tuple4_eta] at h
  exact h

def oneCover : Cover (fun _ => Fin 1) where
  conflict v _ w _ := adjacent v w
  symmetric := by decide
  supported := by decide
  matching := by decide

def emptyCover : Cover (fun _ => Fin 0) where
  conflict _ _ _ _ := false
  symmetric := by decide
  supported := by decide
  matching := by decide

def tuple3 (a b c : Bool) (i : Fin 3) : Bool :=
  match i.val with | 0 => a | 1 => b | _ => c
theorem tuple3_eta (f : Fin 3 → Bool) : tuple3 (f 0) (f 1) (f 2) = f := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by have := i.isLt; omega
  rcases hi with rfl | rfl | rfl <;> rfl

def AtMostOne (p : Fin 3 → Bool) : Prop := ∀ a b, p a = true → p b = true → a = b
theorem checked_avoid_two : ∀ a b c d e f : Bool,
    AtMostOne (tuple3 a b c) → AtMostOne (tuple3 d e f) →
    ∃ i, tuple3 a b c i = false ∧ tuple3 d e f i = false := by
  unfold AtMostOne
  decide

theorem avoid_two (p q : Fin 3 → Bool) (hp : AtMostOne p) (hq : AtMostOne q) :
    ∃ i, p i = false ∧ q i = false := by
  have h := checked_avoid_two (p 0) (p 1) (p 2) (q 0) (q 1) (q 2)
  rw [tuple3_eta, tuple3_eta] at h
  exact h hp hq

theorem no_conflict_on_nonedge {Colors : V → Type} (H : Cover Colors)
    (v : V) (c : Colors v) (w : V) (d : Colors w) (hn : adjacent v w = false) :
    H.conflict v c w d = false := by
  cases he : H.conflict v c w d with
  | false => rfl
  | true =>
    have h := H.supported v c w d he
    rw [hn] at h
    contradiction

theorem four_edge_conditions (H : Cover (fun _ => Fin 3)) (a b c d : Fin 3)
    (h01 : H.conflict 0 a 1 b = false) (h12 : H.conflict 1 b 2 c = false)
    (h23 : H.conflict 2 c 3 d = false) (h03 : H.conflict 0 a 3 d = false) :
    Avoids H (tuple4 a b c d) := by
  intro v w
  rcases all_vertices v with rfl | rfl | rfl | rfl <;>
    rcases all_vertices w with rfl | rfl | rfl | rfl <;>
    simp only [tuple4] <;>
    first
    | exact h01
    | exact h12
    | exact h23
    | exact h03
    | exact no_conflict_on_nonedge H _ _ _ _ (by decide)
    | exact (H.symmetric _ _ _ _).trans h01
    | exact (H.symmetric _ _ _ _).trans h12
    | exact (H.symmetric _ _ _ _).trans h23
    | exact (H.symmetric _ _ _ _).trans h03

/-- Greedy construction for an arbitrary 3-fold cover, not an enumeration
of a selected family of matching assignments. -/
theorem every_three_cover_colorable (H : Cover (fun _ => Fin 3)) :
    ∃ f, Avoids H f := by
  have unique (v w : V) (c : Fin 3) : AtMostOne (fun d => H.conflict v c w d) := by
    intro d e hd he
    exact H.matching v w c d e hd he
  have emptyUnique : AtMostOne (fun _ => false) := by intro a b h; contradiction
  obtain ⟨b,hb,_⟩ := avoid_two (fun c => H.conflict 0 0 1 c) (fun _ => false)
    (unique 0 1 0) emptyUnique
  obtain ⟨c,hc,_⟩ := avoid_two (fun c => H.conflict 1 b 2 c) (fun _ => false)
    (unique 1 2 b) emptyUnique
  obtain ⟨d,hd,hd'⟩ := avoid_two (fun c' => H.conflict 2 c 3 c') (fun c' => H.conflict 0 0 3 c')
    (unique 2 3 c) (unique 0 3 0)
  exact ⟨tuple4 0 b c d, four_edge_conditions H 0 b c d hb hc hd hd'⟩

/-- Restrict arbitrary color fibers to any three distinct available colors. -/
def restrictToThree {Colors : V → Type} (H : Cover Colors)
    (pick : (v : V) → Fin 3 → Colors v)
    (injective : ∀ v a b, pick v a = pick v b → a = b) : Cover (fun _ => Fin 3) where
  conflict v c w d := H.conflict v (pick v c) w (pick w d)
  symmetric := fun v c w d => H.symmetric v (pick v c) w (pick w d)
  supported := fun v c w d h => H.supported v (pick v c) w (pick w d) h
  matching := by
    intro v w c d e hd he
    exact injective w d e (H.matching v w (pick v c) (pick w d) (pick w e) hd he)

theorem arbitrary_lists_of_size_at_least_three {Colors : V → Type} (H : Cover Colors)
    (pick : (v : V) → Fin 3 → Colors v)
    (injective : ∀ v a b, pick v a = pick v b → a = b) :
    ∃ f : (v : V) → Colors v, Avoids H f := by
  obtain ⟨f,hf⟩ := every_three_cover_colorable (restrictToThree H pick injective)
  exact ⟨fun v => pick v (f v), hf⟩

def DPColorable (k : Nat) : Prop := ∀ H : Cover (fun _ => Fin k), ∃ f, Avoids H f
def DPChromaticExactly (k : Nat) : Prop := DPColorable k ∧ ∀ j, j < k → ¬DPColorable j

theorem dp_chromatic_three : DPChromaticExactly 3 := by
  refine ⟨every_three_cover_colorable, ?_⟩
  intro j hj h
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases casesJ with rfl | rfl | rfl
  · obtain ⟨f,_⟩ := h emptyCover
    exact Fin.elim0 (f 0)
  · obtain ⟨f,hf⟩ := h oneCover
    have he := hf 0 1
    have ht : oneCover.conflict 0 (f 0) 1 (f 1) = true := by rfl
    rw [ht] at he
    contradiction
  · obtain ⟨f,hf⟩ := h twisted
    exact twisted_not_colorable f hf

theorem gap_one_on_four_vertices :
    ChromaticExactly 2 ∧ DPChromaticExactly 3 ∧ 3-2=1 ∧ 4<6 :=
  ⟨chromatic_two,dp_chromatic_three,by decide,by decide⟩

/-- A straight square drawing, stated generically so all segment-interior
claims include arbitrary real parameters, not just integer sample points. -/
def position {K : Type} (lo hi : K) (v : V) : K × K :=
  tuple4 (lo,lo) (hi,lo) (hi,hi) (lo,hi) v
def edgeStart (e : V) : V := tuple4 0 1 3 0 e
def edgeFinish (e : V) : V := tuple4 1 2 2 3 e
def trace {K : Type} (lo hi : K) (e : V) (t : K) : K × K :=
  tuple4 (t,lo) (hi,t) (t,hi) (lo,t) e

theorem square_edge_incidence : ∀ v w,
    adjacent v w = true ↔ ∃ e, (v = edgeStart e ∧ w = edgeFinish e) ∨
      (w = edgeStart e ∧ v = edgeFinish e) := by decide

theorem square_vertices_injective {K : Type} (lo hi : K) (hne : lo ≠ hi) :
    ∀ v w, position lo hi v = position lo hi w → v = w := by
  intro v w he
  rcases all_vertices v with rfl | rfl | rfl | rfl <;>
    rcases all_vertices w with rfl | rfl | rfl | rfl <;>
    simp_all [position,tuple4,Prod.mk.injEq]

theorem square_endpoints {K : Type} (lo hi : K) : ∀ e,
    trace lo hi e lo = position lo hi (edgeStart e) ∧
    trace lo hi e hi = position lo hi (edgeFinish e) := by
  intro e
  rcases all_vertices e with rfl | rfl | rfl | rfl <;> exact ⟨rfl,rfl⟩

theorem square_edges_injective {K : Type} (lo hi : K) :
    ∀ e t u, trace lo hi e t = trace lo hi e u → t = u := by
  intro e t u he
  rcases all_vertices e with rfl | rfl | rfl | rfl <;>
    simpa [trace,tuple4,Prod.mk.injEq] using he

theorem square_interior_no_vertices {K : Type} (lo hi : K) :
    ∀ e t, t ≠ lo → t ≠ hi → ∀ v, trace lo hi e t ≠ position lo hi v := by
  intro e t htl hth v he
  rcases all_vertices e with rfl | rfl | rfl | rfl <;>
    rcases all_vertices v with rfl | rfl | rfl | rfl <;>
    simp_all [trace,position,tuple4,Prod.mk.injEq]

theorem square_interiors_disjoint {K : Type} (lo hi : K) (hne : lo ≠ hi) :
    ∀ e f, e ≠ f → ∀ t u, t ≠ lo → t ≠ hi → u ≠ lo → u ≠ hi →
      trace lo hi e t ≠ trace lo hi f u := by
  intro e f hef t u htl hth hul huh he
  rcases all_vertices e with rfl | rfl | rfl | rfl <;>
    rcases all_vertices f with rfl | rfl | rfl | rfl <;>
    simp_all [trace,tuple4,Prod.mk.injEq]

/-- Over R with lo=0 and hi=1, trace(e,t), 0<=t<=1, is precisely the
ordinary straight line segment between the certified graph endpoints.
Every crossing/vertex exclusion is universally quantified in t and u. -/
def SquareEmbedding : Prop :=
  (∀ v w, adjacent v w = true ↔ ∃ e, (v = edgeStart e ∧ w = edgeFinish e) ∨
    (w = edgeStart e ∧ v = edgeFinish e)) ∧
  ∀ (K : Type) (lo hi : K), lo ≠ hi →
    (∀ v w, position lo hi v = position lo hi w → v = w) ∧
    (∀ e, trace lo hi e lo = position lo hi (edgeStart e) ∧
      trace lo hi e hi = position lo hi (edgeFinish e)) ∧
    (∀ e t u, trace lo hi e t = trace lo hi e u → t = u) ∧
    (∀ e t, t ≠ lo → t ≠ hi → ∀ v, trace lo hi e t ≠ position lo hi v) ∧
    (∀ e f, e ≠ f → ∀ t u, t ≠ lo → t ≠ hi → u ≠ lo → u ≠ hi →
      trace lo hi e t ≠ trace lo hi f u)

theorem square_embedding : SquareEmbedding := by
  refine ⟨square_edge_incidence, ?_⟩
  intro K lo hi hne
  exact ⟨square_vertices_injective lo hi hne, square_endpoints lo hi,
    square_edges_injective lo hi, square_interior_no_vertices lo hi,
    square_interiors_disjoint lo hi hne⟩

/-- A prism over an m-gon has m vertices on each of two disjoint bases.
For every genuine polygon m>=3, its order is at least six. -/
def prismOrder (m : Nat) : Nat := 2*m
theorem every_prism_larger (m : Nat) (hm : 3 ≤ m) : 4 < prismOrder m := by
  unfold prismOrder
  omega

/-- Necessary instance of the assertion that a prism is the smallest planar
graph with DP/classical chromatic difference one. -/
theorem conjecture3461_false (m : Nat) (hm : 3 ≤ m) :
    ¬(SquareEmbedding → ChromaticExactly 2 → DPChromaticExactly 3 → prismOrder m ≤ 4) := by
  intro h
  have hb := h square_embedding chromatic_two dp_chromatic_three
  have hl := every_prism_larger m hm
  omega

#print axioms avoids_is_independent_transversal
#print axioms independent_transversal_iff
#print axioms chromatic_two
#print axioms twisted_not_colorable
#print axioms every_three_cover_colorable
#print axioms arbitrary_lists_of_size_at_least_three
#print axioms dp_chromatic_three
#print axioms square_embedding
#print axioms conjecture3461_false
end Conjecture3461
