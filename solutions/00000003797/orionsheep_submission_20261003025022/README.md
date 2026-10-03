# Disproof of conjecture `00000003797`

**Verdict: FALSE — with the claimed optimal step size (the spectral
midpoint 2), the projected gradient method for f(x) = x² DIVERGES:
x_{n+1} = −3xₙ, |xₙ| = 3ⁿ|x₀| → ∞ (3¹⁰ = 59049 > 10⁴ already at
n = 10). Projected gradient does not "always converge".**

## The conjecture (verbatim from `conjectures/00000003797.md`)

> Definition: The projected gradient method denotes the projected
> iteration scheme for variational inequalities. Conjecture: Projected
> gradient always converges uniformly; the optimal step size is the
> midpoint of the spectral interval of the operator, and the convergence
> rate is linear.

## The counterexample

f(x) = x²: the gradient is 2x; the operator x ↦ 2x has spectral
interval [2, 2] with midpoint 2 — the claimed optimal step size. On the
unconstrained domain the projection is the identity, so the iteration is

    x_{n+1} = xₙ − 2·(2xₙ) = −3·xₙ,

with magnitudes |xₙ| = 3ⁿ·|x₀| (kernel-certified closed form, general in
n and x₀). For |x₀| = 1 the magnitude at n = 10 is 3¹⁰ = 59049 > 10⁴ —
kernel-certified. The iterates are unbounded, hence cannot converge:
the "always converges" claim fails, and the spectral midpoint is a
DIVERGENT step, not an optimal one. (The actual optimal step for x² is
1/(2·2) = 1/2 — one-step convergence; classical.)

## Verification

* `reproduce.py` — Monte-Carlo/iteration simulation of the recurrence
  x_{n+1} = −3xₙ (magnitudes 1, 3, 9, 27, … escaping 10⁴ by n = 10), and
  the one-step convergence at the true optimal step 1/2 for contrast.
* Lean 4 (core, v4.33.1) — `lean4/`: the magnitude recurrence, its
  closed form 3ⁿ·|x₀| = |xₙ| (general in n and x₀; the reassociation
  lemmas are self-built by induction — core mul_assoc/mul_left_comm
  carry axioms upstream), the numeric divergence anchor, and the
  refutation. All 8 audited theorems report `does not depend on any
  axioms`. The gradient of x², the spectral interval, and the
  unconstrained-projection convention are classical and cited.

## Boundary

Only the "always converges" and "optimal step = spectral midpoint"
clauses are refuted (via f(x) = x²); genuine convergence theories for
other operators are not addressed.
