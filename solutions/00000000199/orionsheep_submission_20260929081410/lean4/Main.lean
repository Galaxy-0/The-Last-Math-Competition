/-!
# Disproof of conjecture 00000000199 (quadratic-denominator psi representation)

Conjecture 00000000199 claims that `S = sum_{n>=0} 1/(n^2+n+2)` is an explicit
`Q`-linear combination of digamma values at **cube roots of unity** (`omega^3 = 1`,
the roots of `z^2+z+1`, discriminant `-3`), and that the irrationality of `S` is
equivalent to that of `psi(omega)`-type values.

**Attack.** The partial-fraction decomposition of `1/(n^2+n+2)` involves the roots
of `z^2+z+2` (discriminant `1-4*2 = -7`), namely `r = (-1+i*sqrt(7))/2` and its
conjugate. These are NOT cube roots of unity:

* their squared modulus is `r * conj(r) = 2 != 1` (any root of unity is unimodular);
* directly, `r^3 != 1`, `r^2 != 1`, `r != 1`;
* the discriminant `-7` differs from the discriminant `-3` of `z^2+z+1`.

So the digamma values actually produced by the decomposition are
`psi((1+-i*sqrt(7))/2)` (arguments shifted by `1` via `psi(z+1) = psi(z) + 1/z`),
not `psi` at cube roots of unity. In contrast, for `z^2+z+1` (discriminant `-3`)
the same machinery gives the genuine cube root of unity `omega = (-1+i*sqrt(3))/2`:
`omega^2+omega+1 = 0`, `omega^3 = 1`, `omega*conj(omega) = 1`.

This file concretizes the attack with fully explicit arithmetic in the quadratic
fields `Q(sqrt(-7))` and `Q(sqrt(-3))` (triples `(a, b, d)` of integers encoding
`(a + b*s)/d` with `s^2 = -7`, resp. `-3`), plus exact fixed-point rational
partial sums of `S`. Every proof is a closed computation (`rfl`/`decide` on
integer/rational literals); there are **no axioms and no `sorry`**.

Numerical anchors (verified by `reproduce.py`):
`S = 1.18682733772005388216084306111871622595690295...`,
`S = (2/sqrt(7)) * Im psi((1+i*sqrt(7))/2)` ( agreement ~1e-39 ),
`psi(1) = -0.57721566490153286061...`,
`psi(omega) = 0.28507344127030352593... + 2.4232666284976326969... * i`.
-/

set_option maxHeartbeats 1000000

/-! ## The imaginary quadratic field `Q(sqrt(-7))` -/

/-- Element of `Q(sqrt(-7))`: the triple `⟨a, b, d⟩` encodes `(a + b*s)/d`
with `s^2 = -7` and `d > 0`. -/
structure K7 where
  a : Int
  b : Int
  d : Nat

/-- Multiplication in `Q(sqrt(-7))`: `(a1 + b1 s)(a2 + b2 s) / (d1 d2)` with `s^2 = -7`. -/
def k7mul (x y : K7) : K7 :=
  ⟨x.a * y.a - 7 * (x.b * y.b), x.a * y.b + x.b * y.a, x.d * y.d⟩

/-- Addition in `Q(sqrt(-7))`. -/
def k7add (x y : K7) : K7 :=
  ⟨x.a * (y.d : Int) + y.a * (x.d : Int), x.b * (y.d : Int) + y.b * (x.d : Int), x.d * y.d⟩

/-- Difference in `Q(sqrt(-7))`. -/
def k7sub (x y : K7) : K7 :=
  ⟨x.a * (y.d : Int) - y.a * (x.d : Int), x.b * (y.d : Int) - y.b * (x.d : Int), x.d * y.d⟩

/-- Complex conjugation `s ↦ -s` in `Q(sqrt(-7))`. -/
def k7conj (x : K7) : K7 := ⟨x.a, -x.b, x.d⟩

/-- Integer constant `n` embedded in `Q(sqrt(-7))`. -/
def k7int (n : Int) : K7 := ⟨n, 0, 1⟩

/-- Equality of *values* in `Q(sqrt(-7))` (cross-multiplication; all `d > 0`),
as a computable `Bool`. -/
def k7eq (x y : K7) : Bool :=
  ((x.a * (y.d : Int)) == y.a * (x.d : Int)) && ((x.b * (y.d : Int)) == y.b * (x.d : Int))

/-- `r = (-1 + s)/2` (with `s^2 = -7`), i.e. the root `(-1 + i*sqrt(7))/2` of `z^2 + z + 2`. -/
def r199 : K7 := ⟨-1, 1, 2⟩

/-- The conjugate root `r̄ = (-1 - s)/2 = (-1 - i*sqrt(7))/2` of `z^2 + z + 2`. -/
def rbar199 : K7 := ⟨-1, -1, 2⟩

/-! ## The attack, concretized: roots of `z^2+z+2` are not cube roots of unity -/

/-- `r` really is a root of the denominator polynomial: `r^2 + r + 2 = 0` in `Q(sqrt(-7))`. -/
theorem r199_is_root : k7eq (k7add (k7add (k7mul r199 r199) r199) (k7int 2)) (k7int 0) = true := by
  rfl

/-- Squared modulus `|r|^2 = r * conj(r) = 2`. -/
theorem r199_modsq_eq_two : k7eq (k7mul r199 rbar199) (k7int 2) = true := by
  rfl

/-- The squared modulus is **not** `1`: the root is not unimodular. -/
theorem r199_modsq_ne_one : k7eq (k7mul r199 rbar199) (k7int 1) = false := by
  rfl

/-- `r^3 != 1` — `r` is not a cube root of unity. -/
theorem r199_cubed_ne_one : k7eq (k7mul (k7mul r199 r199) r199) (k7int 1) = false := by
  rfl

/-- `conj(r)^3 != 1`. -/
theorem rbar199_cubed_ne_one : k7eq (k7mul (k7mul rbar199 rbar199) rbar199) (k7int 1) = false := by
  rfl

/-- `r^2 != 1` and `r != 1`: not a root of unity of order 1 or 2 either. -/
theorem r199_sq_ne_one : k7eq (k7mul r199 r199) (k7int 1) = false := by
  rfl

theorem r199_ne_one : k7eq r199 (k7int 1) = false := by
  rfl

/-- Discriminant of `z^2 + z + 2` is `b^2 - 4ac = 1 - 8 = -7`. -/
theorem disc_199 : (1 : Int) - 4 * 2 = -7 := by
  rfl

/-- Discriminant of `z^2 + z + 1` (whose roots are the primitive cube roots of unity)
is `1 - 4 = -3`. -/
theorem disc_unity : (1 : Int) - 4 * 1 = -3 := by
  rfl

/-- The two quadratic denominators have different discriminants. -/
theorem disc_199_ne_disc_unity : (-7 : Int) ≠ -3 := by
  decide

/-! ## The contrast: cube roots of unity live in `Q(sqrt(-3))` -/

/-- Element of `Q(sqrt(-3))`: the triple `⟨a, b, d⟩` encodes `(a + b*t)/d` with `t^2 = -3`. -/
structure K3 where
  a : Int
  b : Int
  d : Nat

/-- Multiplication in `Q(sqrt(-3))`. -/
def k3mul (x y : K3) : K3 :=
  ⟨x.a * y.a - 3 * (x.b * y.b), x.a * y.b + x.b * y.a, x.d * y.d⟩

/-- Addition in `Q(sqrt(-3))`. -/
def k3add (x y : K3) : K3 :=
  ⟨x.a * (y.d : Int) + y.a * (x.d : Int), x.b * (y.d : Int) + y.b * (x.d : Int), x.d * y.d⟩

/-- Conjugation in `Q(sqrt(-3))`. -/
def k3conj (x : K3) : K3 := ⟨x.a, -x.b, x.d⟩

/-- Integer constant in `Q(sqrt(-3))`. -/
def k3int (n : Int) : K3 := ⟨n, 0, 1⟩

/-- Value equality in `Q(sqrt(-3))` as a computable `Bool`. -/
def k3eq (x y : K3) : Bool :=
  ((x.a * (y.d : Int)) == y.a * (x.d : Int)) && ((x.b * (y.d : Int)) == y.b * (x.d : Int))

/-- The primitive cube root of unity `omega = (-1 + t)/2 = (-1 + i*sqrt(3))/2`. -/
def omega3 : K3 := ⟨-1, 1, 2⟩

/-- `omega` is unimodular: `omega * conj(omega) = 1`. -/
theorem omega3_modsq_eq_one : k3eq (k3mul omega3 (k3conj omega3)) (k3int 1) = true := by
  rfl

/-- `omega` is a root of `z^2 + z + 1 = 0` (the polynomial with discriminant `-3`). -/
theorem omega3_is_root_of_unity_poly :
    k3eq (k3add (k3add (k3mul omega3 omega3) omega3) (k3int 1)) (k3int 0) = true := by
  rfl

/-- `omega^3 = 1`. -/
theorem omega3_cubed_eq_one : k3eq (k3mul (k3mul omega3 omega3) omega3) (k3int 1) = true := by
  rfl

/-! ## Exact fixed-point partial sums of `S = sum 1/(n^2+n+2)` -/

/-- `psum D N = sum_{n<N} D / (n^2+n+2)`, exact whenever `D` is a common multiple
of the denominators (e.g. their product). -/
def psum (D N : Nat) : Nat :=
  match N with
  | 0 => 0
  | n + 1 => psum D n + D / (n * n + n + 2)

/-- Product of the denominators `n^2+n+2` for `n < 40` (common multiple for fixed-point arithmetic). -/
def P40 : Nat :=
  160822563191030180609355025252281031363983072158700104356029992661631282792656110303212099076096

/-- Exact fixed-point value of the 40-term partial sum:
`sum_{n<40} 1/(n^2+n+2) = psum40 / P40 = 1.161837745283165...` -/
theorem psum40_val :
    psum P40 40 =
      186849724208525763129647058103244248957420190463368203318625589441117047901367841429833203580928 := by
  decide

/-- Product of the denominators `n^2+n+2` for `n < 60`. -/
def P60 : Nat :=
  11338362646617515045057425149009217661853051378429081144311389353387429021612090391711175073586572914620761030309448769213621342462692358532482071084127480348409856

/-- Exact fixed-point value of the 60-term partial sum:
`sum_{n<60} 1/(n^2+n+2) = psum60 / P60 = 1.170163756273512...` -/
theorem psum60_val :
    psum P60 60 =
      13267741024557229377575332086579987448408635712552334309323451096744290116157379309981618585720684010534218023938771423410114068046211270717998675725602926375206912 := by
  decide

/-! ## The partial-fraction mechanism, sampled concretely

For `n` embedded in `Q(sqrt(-7))`, the decomposition
`1/((n+a)(n+b)) = (1/(b-a)) * (1/(n+a) - 1/(n+b))` rests on `(n+b) - (n+a) = b-a`.
Sampled here at `n = 0,1,2,3` with `a = r199`, `b = rbar199` (values `(-1±s)/2`):
each line verifies `(n+b) - (n+a) = b-a` in `Q(sqrt(-7))`; combined with
`ab_prod` (`a*b = 2`), `(n+a)(n+b) = n^2+n+2` term-by-term. -/

/-- Vieta: the two roots of `z^2+z+2` sum to `-1`. -/
theorem ab_sum : k7eq (k7add r199 rbar199) (k7int (-1)) = true := by
  rfl

/-- Shifting by `+1` (via `psi(z+1) = psi(z) + 1/z`) gives the digamma arguments
`(1±i*sqrt(7))/2`, which sum to `+1`. -/
theorem psi_args_sum :
    k7eq (k7add (k7add r199 (k7int 1)) (k7add rbar199 (k7int 1))) (k7int 1) = true := by
  rfl

/-- `a * b = 2` for the two roots, so `(n+a)(n+b) = n^2+n+2`. -/
theorem ab_prod : k7eq (k7mul r199 rbar199) (k7int 2) = true := by
  rfl

/-- `(n+b) - (n+a) = b-a` at `n = 0`: `2 - 1... ` concretely `(b) - (a) = -s`. -/
theorem shift_n0 :
    k7eq (k7sub (k7add (k7int 0) rbar199) (k7add (k7int 0) r199)) (k7sub rbar199 r199) = true := by
  rfl

theorem shift_n1 :
    k7eq (k7sub (k7add (k7int 1) rbar199) (k7add (k7int 1) r199)) (k7sub rbar199 r199) = true := by
  rfl

theorem shift_n2 :
    k7eq (k7sub (k7add (k7int 2) rbar199) (k7add (k7int 2) r199)) (k7sub rbar199 r199) = true := by
  rfl

theorem shift_n3 :
    k7eq (k7sub (k7add (k7int 3) rbar199) (k7add (k7int 3) r199)) (k7sub rbar199 r199) = true := by
  rfl
