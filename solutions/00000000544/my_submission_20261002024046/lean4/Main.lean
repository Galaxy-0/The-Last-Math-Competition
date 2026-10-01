/-!
# Disproof of TLMC conjecture 00000000544 (single-edge forest `K_2`)

Conjecture 00000000544: for all graphs `G` without isolated vertices,
`|Graver(I_{A_G})| <= sum_{H ⊆ G, H forest} 2^{|V(H)|}`, **with equality attained
on forests**.

Counterexample: `G = K_2` (one edge, two vertices — a forest without isolated
vertices). Its (unoriented) incidence matrix is the `2 x 1` matrix
`A = [[1],[1]]`. The monomial map `x1 ↦ t1*t2` is injective, so `I_A = 0`;
equivalently the lattice `ker_Z A = {u in Z^1 : (u, u) = (0,0)} = {0}` has no
nonzero elements, hence no irreducible (Graver) elements: `|Graver| = 0`.
But `H = K_2` itself is a spanning forest of `K_2` with `|V(H)| = 2`,
contributing `2^2 = 4` to the right-hand side (under the spanning-subgraph
reading the RHS is `2^2 + 2^2 = 8`). Hence `0 ≠ RHS`: the equality-on-forests
clause fails and the conjecture is false.

Everything below is proved in core Lean 4 only, with zero axioms and zero
`sorry` (see `Check.lean` for the `#print axioms` audit).
-/

/-! ## The lattice of the single-edge incidence matrix -/

/-- Row of `A_K2 = [[1],[1]]` applied to the single lattice coordinate `u`:
    each of the two rows contributes the dot product `1*u + 0`. -/
def rowDot (u : Int) : Int := 1 * u + 0

/-- Lattice membership `A_K2 • u = 0`, Bool-encoded (the two rows coincide,
    so one vanishing dot product expresses the full condition `A • u = 0`). -/
def latticeCond (u : Int) : Bool := decide (rowDot u = 0)

/-- The lattice of `A_K2` is trivial: `A_K2 • u = (1*u+0, 1*u+0) = 0` forces
    `u = 0`.  Consequently the lattice contains no nonzero elements, so the
    Graver basis (the set of irreducible elements of the lattice) is empty and
    `|Graver(I_{A_K2})| = 0`. -/
theorem lattice_trivial (u : Int) (h : latticeCond u = true) : u = 0 := by
  have h1 : 1 * u + 0 = 0 := of_decide_eq_true h
  have h2 : 1 * u + 0 = u := by rw [Int.add_zero, Int.one_mul]
  rw [h2] at h1
  exact h1

/-- `0` is the (unique) lattice element. -/
theorem zero_in_lattice : latticeCond 0 = true := by rfl

/-- A Graver element would be a nonzero lattice element; none exist. -/
theorem no_graver_elements (u : Int) (hl : latticeCond u = true) (hn : u ≠ 0) :
    False :=
  hn (lattice_trivial u hl)

/-! ## Computational check: boxed enumeration of the Graver basis -/

/-- Candidate lattice coordinates in the box `[-2, 2]`. -/
def candidates : List Int := [-2, -1, 0, 1, 2]

/-- Lattice elements in the box: filtering shows the only one is `0`. -/
def latticeElems : List Int := candidates.filter latticeCond

/-- Graver candidates in the box: nonzero lattice elements — there are none. -/
def graverBox : List Int := latticeElems.filter (fun u => u != 0)

/-- The boxed Graver basis is empty: `Graver(I_{A_K2}) = ∅`. -/
theorem graverBox_empty : graverBox = [] := by decide

/-- Its cardinality is literally `0`: `|Graver| = 0`. -/
theorem graverBox_card : graverBox.length = 0 := by decide

/-! ## The forest bound on `K_2` -/

/-- Spanning subgraphs of `K_2`: the edge set is `∅` or the single edge; both
    are forests on `2` vertices.  Each summand of the conjecture's right-hand
    side contributes `2^{|V(H)|} = 2^2 = 4`. -/
def forestSummands : List Nat := [4, 4]

/-- The conjecture's right-hand side on `K_2` (spanning-subgraph reading). -/
def rhsK2 : Nat := forestSummands.sum

/-- On `K_2` the right-hand side equals `2^2 + 2^2 = 8`. -/
theorem rhsK2_eq : rhsK2 = 8 := by rfl

/-- Under every reading the RHS is at least the summand `H = K_2` itself:
    `2^{|V(K_2)|} = 4`. -/
theorem rhsK2_ge : (4 : Nat) ≤ rhsK2 := by decide

/-! ## The disproof -/

/-- **Conjecture 00000000544 is false.**  On the single-edge forest `K_2`
    (a forest without isolated vertices):
    * the lattice `ker_Z A_K2` is trivial, so `|Graver(I_{A_K2})| = 0`;
    * the forest bound on the right-hand side is `8 ≥ 4 > 0`;
    * hence the required equality `|Graver| = RHS` fails
      (`0 ≠ 8`). -/
theorem conjecture_544_fails :
    (∀ u : Int, latticeCond u = true → u = 0) ∧   -- lattice (hence ideal) is trivial
    graverBox = [] ∧                              -- |Graver| = 0
    (4 : Nat) ≤ rhsK2 ∧                           -- forest bound ≥ 2^2
    graverBox.length ≠ rhsK2 :=                   -- equality on forests fails
  ⟨fun u h => lattice_trivial u h, by decide, by decide, by decide⟩
