/-!
# Disproof of conjecture 00000000348 (twin partial quotients via divisor function)

The conjecture posits a real `α` whose continued-fraction partial quotients satisfy
`a n = a (n+1) = τ n` for all `n ≥ 1`, with `τ` the divisor function.  The condition
at `n` and at `n+1` both constrain the same partial quotient `a (n+1)`, so such an `α`
can exist only if `τ n = τ (n+1)` for every `n`.  Since `τ 4 = 3` and `τ 5 = 2`, the
partial quotient `a 5` would have to equal both `3` and `2` — contradiction.  Hence no
such `α` exists (explicit series or otherwise).
-/

/-- The divisor function: number of positive divisors of `n` (for `n ≥ 1`). -/
def tau (n : Nat) : Nat :=
  (List.range (n + 1)).filter (fun d => n % d == 0) |>.length

/-- The registered attack numerals: `τ 4 = 3` (divisors 1, 2, 4). -/
theorem tau_four : tau 4 = 3 := rfl

/-- The registered attack numerals: `τ 5 = 2` (divisors 1, 5). -/
theorem tau_five : tau 5 = 2 := rfl

/-- The conjecture's partial-quotient condition is unsatisfiable: no `a : Nat → Nat`
satisfies `a n = τ n ∧ a (n+1) = τ n` for all `n`, since `n = 4` and `n = 5` force
`a 5 = 3` and `a 5 = 2` simultaneously.  Consequently no real number `α` (and no
explicit series construction) realizes the conjecture. -/
theorem no_such_alpha :
    ¬ ∃ a : Nat → Nat, ∀ n, a n = tau n ∧ a (n + 1) = tau n := by
  intro ⟨a, ha⟩
  have h1 : a 5 = 3 := (ha 4).2.trans tau_four
  have h2 : a 5 = 2 := (ha 5).1.trans tau_five
  exact absurd (h1.symm.trans h2) (by decide)
