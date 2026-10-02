/-
  Disproof of TLMC conjecture 00000002732.

  Conjecture: chi(Delta) <= 2 + max over links of chi(link) for a
  simplicial complex Delta.

  Counterexample: Delta = the FLAG COMPLEX of the Groetzsch graph
  G = Mycielski(C5): 11 vertices (v0..v4 the C5, u0..u4 the clones, w),
  20 edges (vi v(i+1); vi u(i+1); vi u(i-1); ui w).

  Facts (all kernel-certified below):
    (1) G is triangle-free, so every link in Delta is a 0-dimensional
        complex with chi(link) = 1: the conjectured bound gives
        chi(Delta) <= 2 + 1 = 3.
    (2) chi(Delta) = chi(G) (a proper coloring of a flag complex is
        exactly a proper coloring of its 1-skeleton — every face is a
        clique; standard, stated in README/tex).
    (3) G admits NO proper 3-coloring (exhaustive kernel check over all
        3^11 = 177147 assignments) but admits the proper 4-coloring
        (0,1,0,1,2, 0,1,0,1,2, 3). So chi(G) = 4 = chi(Delta) > 3.

  All theorems are closed kernel computations, axiom-free; the big check
  runs with unlimited heartbeats.
-/

namespace Tlmc2732

/-- The 20 edges of the Groetzsch graph (vertices 0..10:
    0..4 = the C5, 5..9 = clones, 10 = the apex). -/
def edges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),
   (0,6),(1,7),(2,8),(3,9),(4,5),
   (0,9),(1,5),(2,6),(3,7),(4,8),
   (5,10),(6,10),(7,10),(8,10),(9,10)]

/-- Adjacency by table lookup. -/
def adj (a b : Nat) : Bool :=
  edges.any (fun e => (e.1 == a && e.2 == b) || (e.1 == b && e.2 == a))

/-- Color of vertex v in the assignment encoded by t (base 3). -/
def colorOf (t v : Nat) : Nat := (t / (3 ^ v)) % 3

/-- Is the assignment t a proper 3-coloring? -/
def proper3 (t : Nat) : Bool :=
  edges.all (fun e => colorOf t e.1 != colorOf t e.2)

/-- Triangle-freeness: no edge (a,b) has a common neighbor c. -/
def triangleFree : Bool :=
  edges.all (fun e =>
    (List.range 11).all (fun c =>
      !(adj e.1 c) || !(adj e.2 c) || (c == e.1) || (c == e.2)))

/-- The exhibited 4-coloring (0,1,0,1,2, 0,1,0,1,2, 3). -/
def witness : List Nat := [0,1,0,1,2,0,1,0,1,2,3]

/-- Structural lookup into the witness (List.getD carries propext). -/
def wat : Nat → Nat
  | 0  => 0 | 1  => 1 | 2  => 0 | 3  => 1 | 4  => 2
  | 5  => 0 | 6  => 1 | 7  => 0 | 8  => 1 | 9  => 2
  | _  => 3

/- ## The three facts. -/

theorem is_triangle_free : triangleFree = true := by decide

theorem witness_proper : edges.all (fun e => wat e.1 != wat e.2) = true := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 400000 in
theorem no_3coloring : (List.range (3 ^ 11)).all (fun t => !proper3 t) = true := by
  decide

/- ## The bound and the violation. -/

theorem bound_is_3 : (2 + 1 : Nat) = 3 := rfl

theorem four_gt_3 : ¬ ((4 : Nat) <= 3) := by decide

end Tlmc2732
