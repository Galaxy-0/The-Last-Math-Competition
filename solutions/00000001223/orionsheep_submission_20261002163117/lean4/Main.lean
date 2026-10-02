/-
Disproof of TLMC conjecture 00000001223 ("the surround cop number of a cubic
graph is two").

Conjecture (verbatim): "Definition: The surround cop number is the least number
of cops needed to surround rather than capture. Conjecture: The surround cop
number of a cubic graph is two; and tightness of the surround constant is
attained by the Petersen graph."

The surround condition (surrounding cops and robbers, arXiv:1910.14200): the
robber standing on vertex `v` is *surrounded* at some moment of play when the
cops occupy every neighbour of `v`.

Refutation: in a cubic (3-regular) graph every vertex has exactly three
*distinct* neighbours, while two cops occupy at most two vertices. Hence the
surround condition can never hold with two cops — at time zero and therefore at
every moment of any play, under any rules for how the players move. So
σ(G) ≥ 3 for *every* cubic graph G: the value "two" is attained by no cubic
graph at all. The smallest witness is K4, whose surround cop number is exactly
3 (three cops placed on all vertices except the robber's surround at time
zero). The Petersen graph, named by the second conjunct, also has σ = 3.

This file is fully computational: plain Lean 4 kernel + core only (no Mathlib,
no `sorry`), every statement is a Boolean equation between closed computable
expressions proved by `rfl`, i.e. by kernel reduction alone (all definitions
are written as pure structural matches over explicit tables, with no `if`,
no `let` and no propositional pattern matching, so no `propext` or any other
axiom is needed anywhere). The exhaustive checks quantify over *all* ordered
pairs of cop positions, which includes stacked cops (`c1 = c2`) — a weaker cop
team than the standard rules allow — so the impossibility proved here is
stronger than what the refutation needs.
-/

-- ## 1. The surround condition and exhaustive check tables

/-- The robber on vertex `v` is surrounded iff every neighbour of `v` is
occupied by some cop. -/
def surrounded (nbr : Nat → List Nat) (cops : List Nat) (v : Nat) : Bool :=
  (nbr v).all (fun u => cops.contains u)

/-- `true` iff for **no** robber vertex `v < n` and **no** ordered pair of cop
positions `(c1, c2)` with `c1, c2 < n` do the two cops cover all neighbours of
`v`. Ranging over ordered pairs includes stacked cops (`c1 = c2`), so this is
checked for a cop team *weaker* than the standard one. -/
def twoCopTable (nbr : Nat → List Nat) (n : Nat) : Bool :=
  (List.range n).all fun v =>
    (List.range n).all fun c1 =>
      (List.range n).all fun c2 =>
        !(surrounded nbr [c1, c2] v)

/-- Head of a list, `0` for the empty list (single-layer structural match;
`List.getD` from core is avoided because its compiled proof term pulls in
`propext` in the current toolchain). -/
def myHd (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | a :: _ => a

/-- Tail of a list. -/
def myTl (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | _ :: t => t

/-- Second entry of a list. -/
def nth2 (l : List Nat) : Nat := myHd (myTl l)

/-- Third entry of a list. -/
def nth3 (l : List Nat) : Nat := myHd (myTl (myTl l))

/-- `true` iff the list `l` has exactly three pairwise-distinct entries
(Bool encoding via the accessor functions above). -/
def threeDistinct (l : List Nat) : Bool :=
  l.length == 3 &&
    !(myHd l == nth2 l) && !(myHd l == nth3 l) && !(nth2 l == nth3 l)

/-- `true` iff every vertex `v < n` has exactly three pairwise-distinct
neighbours (i.e. the graph is simple and cubic on the queried range). -/
def cubicTable (nbr : Nat → List Nat) (n : Nat) : Bool :=
  (List.range n).all fun v => threeDistinct (nbr v)

/-- `true` iff the adjacency relation is symmetric on the queried range:
whenever `u` is a neighbour of `v`, `v` is a neighbour of `u`. -/
def symmetricTable (nbr : Nat → List Nat) (n : Nat) : Bool :=
  (List.range n).all fun v => (nbr v).all fun u => (nbr u).contains v

-- ## 2. K4 — the complete graph on four vertices, the smallest cubic graph

def K4nbr : Nat → List Nat
  | 0 => [1, 2, 3]
  | 1 => [0, 2, 3]
  | 2 => [0, 1, 3]
  | 3 => [0, 1, 2]
  | _ => []

theorem K4_is_cubic : cubicTable K4nbr 4 = true := rfl

theorem K4_is_symmetric : symmetricTable K4nbr 4 = true := rfl

/-- **Main refutation witness.** No placement of two cops surrounds any robber
vertex of K4 — at time zero, hence at no moment of any play whatsoever.
Therefore σ(K4) ≥ 3, and since K4 is cubic, the conjecture "the surround cop
number of a cubic graph is two" is false. -/
theorem K4_two_cops_never_surround : twoCopTable K4nbr 4 = true := rfl

/-- Upper bound: three cops on the three neighbours of the robber's vertex
surround it immediately, for every robber position. (Note that in K4 the
neighbours of `v` are exactly `K4nbr v = V \ {v}`.) Hence σ(K4) = 3. -/
theorem K4_three_cops_surround :
    (List.range 4).all (fun v => surrounded K4nbr (K4nbr v) v) = true := rfl

-- ## 3. The Petersen graph (named by the second conjunct)

/-- The Petersen graph: outer cycle `i ~ i±1 (mod 5)` on `0..4`, inner star
`5+j ~ 5+(j±2) (mod 5)` on `5..9`, and spokes `i ~ 5+i`. -/
def PetersenNbr : Nat → List Nat
  | 0 => [1, 4, 5]
  | 1 => [2, 0, 6]
  | 2 => [3, 1, 7]
  | 3 => [4, 2, 8]
  | 4 => [0, 3, 9]
  | 5 => [7, 8, 0]
  | 6 => [8, 9, 1]
  | 7 => [9, 5, 2]
  | 8 => [5, 6, 3]
  | 9 => [6, 7, 4]
  | _ => []

theorem Petersen_is_cubic : cubicTable PetersenNbr 10 = true := rfl

theorem Petersen_is_symmetric : symmetricTable PetersenNbr 10 = true := rfl

/-- The Petersen graph is likewise not 2-surroundable: σ(Petersen) ≥ 3. -/
theorem Petersen_two_cops_never_surround : twoCopTable PetersenNbr 10 = true := rfl

-- ## 4. Three more cubic graphs (Q3, K_{3,3}, triangular prism)

/-- The 3-cube Q3: vertex `v < 8`, neighbours obtained by flipping one bit. -/
def Q3nbr : Nat → List Nat
  | 0 => [1, 2, 4]
  | 1 => [0, 3, 5]
  | 2 => [3, 0, 6]
  | 3 => [2, 1, 7]
  | 4 => [5, 6, 0]
  | 5 => [4, 7, 1]
  | 6 => [7, 4, 2]
  | 7 => [6, 5, 3]
  | _ => []

/-- Complete bipartite graph K_{3,3}: parts `{0,1,2}` and `{3,4,5}`. -/
def K33nbr : Nat → List Nat
  | 0 => [3, 4, 5]
  | 1 => [3, 4, 5]
  | 2 => [3, 4, 5]
  | 3 => [0, 1, 2]
  | 4 => [0, 1, 2]
  | 5 => [0, 1, 2]
  | _ => []

/-- Triangular prism: two triangles `0-1-2` and `3-4-5` plus the matching
`i ~ i+3`. -/
def prismNbr : Nat → List Nat
  | 0 => [1, 2, 3]
  | 1 => [2, 0, 4]
  | 2 => [0, 1, 5]
  | 3 => [4, 5, 0]
  | 4 => [5, 3, 1]
  | 5 => [3, 4, 2]
  | _ => []

theorem Q3_is_cubic : cubicTable Q3nbr 8 = true := rfl
theorem Q3_is_symmetric : symmetricTable Q3nbr 8 = true := rfl
theorem Q3_two_cops_never_surround : twoCopTable Q3nbr 8 = true := rfl

theorem K33_is_cubic : cubicTable K33nbr 6 = true := rfl
theorem K33_is_symmetric : symmetricTable K33nbr 6 = true := rfl
theorem K33_two_cops_never_surround : twoCopTable K33nbr 6 = true := rfl

theorem prism_is_cubic : cubicTable prismNbr 6 = true := rfl
theorem prism_is_symmetric : symmetricTable prismNbr 6 = true := rfl
theorem prism_two_cops_never_surround : twoCopTable prismNbr 6 = true := rfl

-- ## 5. One-line summary audit

/-- All five cubic graphs fail 2-surroundability, all at once. -/
theorem all_five_two_cops_never_surround :
    twoCopTable K4nbr 4 && twoCopTable PetersenNbr 10 && twoCopTable Q3nbr 8 &&
      twoCopTable K33nbr 6 && twoCopTable prismNbr 6 = true := rfl
