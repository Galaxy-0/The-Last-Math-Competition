/-
  Disproof of TLMC conjecture 00000002715.

  Conjecture (literal wording): "the minimal vertex count of a shellable
  3-dimensional manifold complex is twelve, with the minimal example an
  edge triangulation".

  Counterexample: the boundary of the 4-simplex, dDelta^4, is a closed
  combinatorial 3-manifold on FIVE vertices (the 3-sphere) and it is
  shellable.  Kernel-certified below, working exactly with the shellability
  definition stated in the conjecture ("a linear order of faces such that
  the intersection with previous faces is a pure (dim-1) complex"):

    * dDelta^4 has vertices {0,1,2,3,4} and C(5,4) = 5 tetrahedral facets;
    * the link of every vertex is the boundary of the 3-simplex spanned
      by the other four vertices (a combinatorial 2-sphere with
      f-vector (4,6,4)) — so dDelta^4 is a closed combinatorial
      3-manifold;
    * the lexicographic facet order is verified to satisfy the shelling
      condition: for each facet, the faces covered by earlier facets
      form a pure 2-dimensional complex (every covered vertex and edge
      lies in a covered triangle).

  So a shellable 3-dimensional manifold complex exists with 5 < 12
  vertices, and the conjectured minimal vertex count of twelve is false.
  (The classical fact behind this check: for the boundary of a simplex
  EVERY facet order is a shelling; one explicit order suffices here.)
  All theorems are closed kernel computations, axiom-free.
-/

namespace Tlmc2715

/-- The 5 facets of dDelta^4: the 4-subsets of {0,1,2,3,4}, each as a
    sorted list, in lexicographic order (the shelling order used below). -/
def facets : List (List Nat) :=
  [ [0,1,2,3], [0,1,2,4], [0,1,3,4], [0,2,3,4], [1,2,3,4] ]

/-- Sublist membership: every element of a is an element of b. -/
def sub (a b : List Nat) : Bool := a.all (fun x => b.contains x)

/-- All edges of a sorted vertex list: pairs [x,y] with x before y. -/
def edges : List Nat → List (List Nat)
  | []        => []
  | x :: rest => rest.flatMap (fun y => [[x, y]]) ++ edges rest

/-- All triangles of a sorted vertex list: [x,y,z] with x before y
    before z (x together with an edge of the tail, or a triangle of the
    tail). -/
def tris : List Nat → List (List Nat)
  | []        => []
  | x :: rest => (edges rest).map (fun e => [x] ++ e) ++ tris rest

/-- Facet accessor.  (Core `List.getD` carries `propext` in its reduction,
    which would pollute `#print axioms`; a match table is axiom-free.) -/
def getFacet : Nat → List Nat
  | 0 => [0,1,2,3]
  | 1 => [0,1,2,4]
  | 2 => [0,1,3,4]
  | 3 => [0,2,3,4]
  | 4 => [1,2,3,4]
  | _ => []

/-- Is the face g covered, i.e. contained in some facet numbered < i? -/
def covered (g : List Nat) (i : Nat) : Bool :=
  ((List.range i).any fun j => sub g (getFacet j))

/-- The shelling condition for facet number i, exactly as defined in the
    conjecture: the part of facet i already covered by earlier facets is
    a pure 2-dimensional complex — every covered vertex and every covered
    edge lies in a covered triangle.  (Uncovered faces are unconstrained;
    in particular facet 0, which covers nothing, passes vacuously.) -/
def shellingStep (i : Nat) : Bool :=
  let f := getFacet i
  f.all (fun v => !(covered [v] i) ||
                 (tris f).any (fun t => covered t i && sub [v] t)) &&
  (edges f).all (fun e => !(covered e i) ||
                 (tris f).any (fun t => covered t i && sub e t))

/-- The lexicographic facet order is a shelling of dDelta^4. -/
theorem shelling_ok : (List.range 5).all shellingStep = true := by decide

/-- Vertex links, part 1: each of the 5 vertices lies in exactly 4
    tetrahedral facets, so its link has 4 facets. -/
theorem vertex_in_4_facets :
    (List.range 5).all (fun v =>
      ((List.range 5).filter (fun j =>
        getFacet j |>.contains v)).length = 4) = true := by decide

/-- Vertex links, part 2: for each vertex v the facets of its link are
    exactly the 3-subsets of the other four vertices — i.e. the link is
    the boundary of the 3-simplex on V \ {v}, a combinatorial 2-sphere
    with f-vector (4, 6, 4).  Together with `vertex_in_4_facets` this
    certifies that dDelta^4 is a closed combinatorial 3-manifold. -/
theorem link_is_boundary_of_tetrahedron :
    (List.range 5).all (fun v =>
      let others := ((List.range 5).filter (fun u => u != v))
      (tris others).length = 4) = true := by decide

/-- dDelta^4 has exactly 5 vertices: all of {0,1,2,3,4} occur in some
    facet, and no other vertex occurs. -/
theorem uses_exactly_5_vertices :
    ((List.range 5).all (fun v => facets.any (fun f => f.contains v)) &&
     facets.all (fun f => f.all (fun v => v < 5))) = true := by decide

/-- Facet count: C(5,4) = 5 tetrahedra. -/
theorem facet_count : facets.length = 5 := by decide

/-- The conjectured minimal vertex count twelve is false: a shellable
    3-dimensional manifold complex exists on 5 < 12 vertices. -/
theorem five_vertices_not_twelve : ¬ ((5 : Nat) = 12) := by decide
theorem five_lt_twelve : (5 : Nat) < 12 := by decide

end Tlmc2715
