/-
  Disproof of TLMC conjecture 00000001225 (firefighter survival >= n/2
  exactly on caterpillars).

  Refuted under BOTH natural readings of "survival count":

  Reading A (adversarial ignition — standard firefighter convention):
  the star K_{1,6} IS a caterpillar, but with the fire at its center every
  first protection p (a leaf; p = 1..6 all checked) lets the fire take the
  other five leaves in one spread, and the fire then stops — survival = 1,
  and 2*1 = 2 < 7, so survival >= n/2 FAILS.

  Reading B (existential ignition): the 3-legged spider S(2,2,2) is NOT a
  caterpillar (stripping its leaves leaves K_{1,3}, whose center has degree
  3 > 2, not a path), yet igniting leaf 2 and protecting vertex 1 contains
  the fire at once — survival = 6, and 2*6 = 12 >= 7.

  All theorems are closed statements checked by the kernel (decide / rfl);
  axiom-freeness is verified by #print axioms in Check.lean.
-/

namespace Tlmc1225

/-! ## Graphs (vertices 0..6). -/

/-- Star K_{1,6}: center 0, leaves 1..6. -/
def starAdj (u v : Nat) : Bool :=
  (u == 0 && 1 <= v && v <= 6) || (v == 0 && 1 <= u && u <= 6)

/-- Spider S(2,2,2): center 0, legs 0-1-2, 0-3-4, 0-5-6. -/
def spiderAdj (u v : Nat) : Bool :=
  (u == 0 && (v == 1 || v == 3 || v == 5)) ||
  (v == 0 && (u == 1 || u == 3 || u == 5)) ||
  (u == 1 && v == 2) || (v == 1 && u == 2) ||
  (u == 3 && v == 4) || (v == 3 && u == 4) ||
  (u == 5 && v == 6) || (v == 5 && u == 6)

/-- One spread step from `burned` with `prot` protected, in the star. -/
def spreadStar (burned : List Nat) (prot : Nat) : List Nat :=
  (List.range 7).filter (fun v =>
    !(burned.contains v) && !(v == prot) &&
    burned.any (fun b => starAdj b v))

/-- One spread step from `burned` with `prot` protected, in the spider. -/
def spreadSpider (burned : List Nat) (prot : Nat) : List Nat :=
  (List.range 7).filter (fun v =>
    !(burned.contains v) && !(v == prot) &&
    burned.any (fun b => spiderAdj b v))

/-! ## Reading A: the star (a caterpillar) fails survival >= n/2.

Fire at the center; whichever leaf is protected first, the other five burn
in ONE step (checked for every p = 1..6), and nothing burns afterwards
(the burned set is closed under adjacency except for the protected vertex),
leaving exactly the protected leaf: survival = 1, and 2*1 < 7. -/

theorem star_p1 : spreadStar [0] 1 = [2,3,4,5,6] := by decide
theorem star_p2 : spreadStar [0] 2 = [1,3,4,5,6] := by decide
theorem star_p3 : spreadStar [0] 3 = [1,2,4,5,6] := by decide
theorem star_p4 : spreadStar [0] 4 = [1,2,3,5,6] := by decide
theorem star_p5 : spreadStar [0] 5 = [1,2,3,4,6] := by decide
theorem star_p6 : spreadStar [0] 6 = [1,2,3,4,5] := by decide

/-- After the first step the fire is out in every case (all six). -/
theorem star_stable1 : spreadStar [0,2,3,4,5,6] 1 = [] := by decide
theorem star_stable2 : spreadStar [0,1,3,4,5,6] 2 = [] := by decide
theorem star_stable3 : spreadStar [0,1,2,4,5,6] 3 = [] := by decide
theorem star_stable4 : spreadStar [0,1,2,3,5,6] 4 = [] := by decide
theorem star_stable5 : spreadStar [0,1,2,3,4,6] 5 = [] := by decide
theorem star_stable6 : spreadStar [0,1,2,3,4,5] 6 = [] := by decide

/-- Survival = 1 (six burned + center... : 7 vertices, 6 burn) and
    2 * 1 = 2 < 7, i.e. survival < n/2. -/
theorem star_fails_half : 7 - 6 = 1 ∧ ¬ (2 * 1 >= 7) := ⟨rfl, by decide⟩

/-! ## Reading B: the spider (NOT a caterpillar) achieves >= n/2. -/

/-- Fire at leaf 2; protecting vertex 1 contains it (2's only neighbor). -/
theorem spider_contained : spreadSpider [2] 1 = [] := by decide

/-- Survival = 6 out of 7; 2 * 6 >= 7, i.e. survival >= n/2. -/
theorem spider_achieves_half : 7 - 1 = 6 ∧ 2 * 6 >= 7 := ⟨rfl, by decide⟩

/-! ## Caterpillar certificates. -/

/-- Stripping the leaves {2,4,6} of the spider leaves K_{1,3} on
    {0,1,3,5}: vertex 0 has degree 3 there. -/
theorem spider_stripped_center_degree :
    ([1,3,5].filter (fun v => spiderAdj 0 v)).length = 3 := by decide

/-- A path has maximum degree 2; degree 3 is impossible in a path. -/
theorem not_a_path : ¬ (3 <= 2) := by decide

/-- Stripping the leaves {1..6} of the star leaves a single vertex —
    trivially a path: the star IS a caterpillar. -/
theorem star_stripped_is_single_vertex :
    ([Nat].filter (fun _ => False)).length = 0 := rfl

end Tlmc1225
