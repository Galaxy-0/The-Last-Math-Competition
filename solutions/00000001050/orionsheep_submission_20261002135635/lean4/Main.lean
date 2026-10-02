/-!
# Disproof of TLMC conjecture 00000001050

Conjecture (verbatim): "For any composition of a permutation polynomial `f` with a
linearized polynomial, the image under the relative trace `F_{q^2}/F_q` is everything
if and only if the kernel is trivial (a relative-trace surjectivity criterion)."

Counterexample: `q = 2`, `F4 = F2(omega)` with `omega^2 = omega + 1`.
Permutation polynomial `f = id`; linearized polynomial `L(x) = omega*x + omega*x^2`
(exponents `2^0, 2^1`), so the composition `g = L ∘ id = L` (both orders coincide).
Then:
* `ker L = {x : x + x^2 = 0} = {0, 1}` is NONtrivial;
* `Tr_{F4/F2}(L(F4)) = {Tr(0), Tr(omega)} = {0, omega + omega^2} = {0, 1} = F2`
  is everything (surjective onto the prime field).

Hence "image is everything iff kernel is trivial" is FALSE.

`F4` is a 4-constructor inductive type with explicit field tables, so every
assertion below holds by `rfl` / constructor exhaustion: no `sorry`, no axioms
(no `Classical`, no `propext`, no `Quot.sound`).
-/

/-- The four elements of `F4 = F2(omega)`: `z` = 0, `o` = 1,
`w` = omega, `w2` = omega^2 = 1 + omega. -/
inductive F4
  | z
  | o
  | w
  | w2

namespace F4

/-- Addition in `F4` (characteristic 2; `1 + omega = omega^2`,
`omega + omega = 0`, `omega + omega^2 = 1`). -/
def add : F4 → F4 → F4
  | z, x => x
  | x, z => x
  | o, o => z
  | o, w => w2
  | w, o => w2
  | o, w2 => w
  | w2, o => w
  | w, w => z
  | w, w2 => o
  | w2, w => o
  | w2, w2 => z

/-- Multiplication in `F4` (`omega * omega = omega^2`, `omega^3 = 1`),
given as an explicit 16-row table. (Wildcards/overlaps in the pattern matrix
make the equation compiler emit auxiliary matchers whose reduction drags in
`propext`; the fully explicit table keeps every `rfl` axiom-free.) -/
def mul : F4 → F4 → F4
  | z, z  => z
  | z, o  => z
  | z, w  => z
  | z, w2 => z
  | o, z  => z
  | o, o  => o
  | o, w  => w
  | o, w2 => w2
  | w, z  => z
  | w, o  => w
  | w, w  => w2
  | w, w2 => o
  | w2, z => z
  | w2, o => w2
  | w2, w => o
  | w2, w2 => w

/-- Frobenius squaring `x ↦ x^2` (`omega^2 ↦ omega^4 = omega`). -/
def sq : F4 → F4
  | z => z
  | o => o
  | w => w2
  | w2 => w

/-- The relative trace `Tr_{F4/F2}(x) = x + x^2` (here `q = 2`). -/
def trace (x : F4) : F4 := add x (sq x)

/-- The composition `g = L ∘ f` with permutation polynomial `f = id` and
linearized polynomial `L(x) = omega * (x + x^2) = omega*x + omega*x^2`.
(Since `f = id`, `L ∘ id = id ∘ L = L`.) -/
def lin (x : F4) : F4 := mul w (add x (sq x))

/-- The map whose image the conjecture discusses: `Tr_{F4/F2} ∘ L ∘ f`. -/
def trCompose (x : F4) : F4 := trace (lin x)

/-- The conjecture's right-hand side, for `g = L ∘ id`: the kernel of the
composition is trivial. (With `f = id` this is also the kernel of the
linearized polynomial itself.) -/
def KernelTrivial : Prop := ∀ x, lin x = z → x = z

/-- The conjecture's left-hand side: the image of `Tr ∘ g` is "everything",
i.e. contains every element of the prime field `F2 = {0, 1} = {z, o}`. -/
def TraceSurjective : Prop := ∀ y : F4, y = z ∨ y = o → ∃ x, trCompose x = y

/-! ### Concrete attack table (all closed by `rfl`) -/

/-- `L(0) = 0`. -/
theorem lin_zero : lin z = z := rfl

/-- `L(1) = omega*(1 + 1) = 0`, so `1 ∈ ker L`. -/
theorem lin_one : lin o = z := rfl

/-- `L(omega) = omega*(omega + omega^2) = omega*1 = omega`. -/
theorem lin_w : lin w = w := rfl

/-- `L(omega^2) = omega*(omega^2 + omega) = omega*1 = omega`. -/
theorem lin_w2 : lin w2 = w := rfl

/-- `Tr(omega) = omega + omega^2 = 1`. -/
theorem trace_w : trace w = o := rfl

/-- `Tr(L(0)) = Tr(0) = 0`. -/
theorem trCompose_zero : trCompose z = z := rfl

/-- `Tr(L(omega)) = Tr(omega) = 1`. -/
theorem trCompose_w : trCompose w = o := rfl

/-- Distinctness of `1` and `0` in `F4`. -/
theorem one_ne_zero : o ≠ z := by
  intro h
  cases h

/-! ### The two halves -/

/-- Surjectivity half: TRUE. `Tr(L(0)) = 0` and `Tr(L(omega)) = 1`, so the
image of `Tr ∘ L ∘ id` contains all of `F2 = {0, 1}`. -/
theorem surjective_true : TraceSurjective := by
  intro y hy
  cases hy with
  | inl h => exact ⟨z, h.symm⟩
  | inr h => exact ⟨w, h.symm⟩

/-- Kernel half: NONtrivial. `1 ∈ ker L` (since `1 + 1^2 = 0`) and `1 ≠ 0`,
so the kernel of the composition is not trivial. -/
theorem kernel_not_trivial : ¬ KernelTrivial := by
  intro h
  exact one_ne_zero (h o rfl)

/-- Main result: the conjecture's criterion
"trace image is everything **iff** kernel is trivial" is FALSE for the
composition of the permutation polynomial `f = id` with the linearized
polynomial `L(x) = omega(x + x^2)` over `F4/F2`. -/
theorem criterion_false : ¬ (TraceSurjective ↔ KernelTrivial) := by
  intro h
  exact kernel_not_trivial (h.mp surjective_true)

end F4
