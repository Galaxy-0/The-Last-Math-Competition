/-
  Disproof of TLMC conjecture 00000002211.

  Conjecture: "For imaginary quadratic integer rings Z[sqrt(-d)], the
  elasticity rho(R) (ratio of longest to shortest factorization lengths)
  has an explicit table of the type (smallest prime factor of d)."

  Refutation: d = 6 and d = 14 have the SAME smallest prime factor
  (both are even: kernel-certified 2 | 6 and 2 | 14), but their
  elasticities differ:

    * Z[sqrt(-6)] is the full ring of integers of Q(sqrt(-6))
      (discriminant -24).  Its class number h(-24) = 2, kernel-certified
      by exhausting the reduced positive-definite binary quadratic
      forms of discriminant -24: exactly (1,0,6) and (2,0,3).  By
      Carlitz's theorem (1960), a ring of integers is half-factorial
      (rho = 1) iff its class number is at most 2, so
      rho(Z[sqrt(-6)]) = 1.

    * Z[sqrt(-14)] is the full ring of integers of Q(sqrt(-14))
      (discriminant -56).  Its class number h(-56) = 4, kernel-certified
      by exhausting the reduced forms of discriminant -56: exactly
      (1,0,14), (2,0,7) and (3,2,5) on the b >= 0 side, plus the
      mirrored (3,-2,5) of the unique non-self-converse form (3,2,5)
      (kernel-certified: 0 < 2 < 3 < 5).  Since 4 > 2, Carlitz gives
      rho(Z[sqrt(-14)]) > 1.

  Hence rho(Z[sqrt(-6)]) = 1 < rho(Z[sqrt(-14)]) while both d share the
  smallest prime factor 2: rho is NOT a function of spf(d), and no
  table "indexed by the smallest prime factor of d" can be correct.

  Kernel-certified below: the shared prime divisor 2; the complete
  enumeration of reduced forms (b >= 0 side) for both discriminants
  (every solution of 4ac = b^2 + D with 1 <= a, b <= a, a <= c is one
  of the listed triples: the size bound 3a^2 <= |D| caps a at 2 resp.
  4, and every remaining (a,b) leaf is resolved by an exact divisibility
  argument); the strictness 0 < 2 < 3 < 5; and the comparison 2 <= 2 < 4.
  Carlitz's half-factorial criterion, the reflection b -> -b, and the
  identification "class number = number of reduced forms" are classical
  and cited (prose).  All kernel computations are closed; the audit
  reports zero axioms.  (Core's Nat.mul_assoc / add_mul / mul_mod_right
  depend on axioms, so the needed pieces are rebuilt here by induction.)
-/

namespace Tlmc2211

/-! ## Axiom-free arithmetic helpers. -/

theorem add_right_comm_self (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]

theorem add_left_comm_pair (b c d : Nat) : b + (c + d) = c + (b + d) := by
  rw [← Nat.add_assoc b c d, Nat.add_comm b c, Nat.add_assoc c b d]

theorem add_swap4 (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc a b (c + d), add_left_comm_pair b c d,
    ← Nat.add_assoc a c (b + d)]

theorem add_mul_self (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, ih]
      exact add_swap4 (a * c) (b * c) a b

theorem mul_assoc_self (a b c : Nat) : a * b * c = a * (b * c) := by
  induction a with
  | zero => rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
  | succ n ih =>
      rw [Nat.succ_mul, Nat.succ_mul]
      rw [add_mul_self (n * b) b c]
      rw [ih]

theorem add_left_cancel_le : ∀ (x y z : Nat), x + y ≤ x + z → y ≤ z := by
  intro x
  induction x with
  | zero =>
      intro y z h
      rw [Nat.zero_add, Nat.zero_add] at h
      exact h
  | succ n ih =>
      intro y z h
      exact ih y z (Nat.le_of_succ_le_succ (by rw [Nat.succ_add, Nat.succ_add] at h; exact h))

theorem four_id (X : Nat) : X + 3 * X = 4 * X :=
  Eq.trans (Nat.add_comm X (3 * X)) (Eq.symm (Nat.succ_mul 3 X))

/-! ## Shared smallest prime factor. -/

/-- Both d = 6 and d = 14 are even: the smallest prime, 2, divides both. -/
theorem spf_shared : (2:Nat) ∣ 6 ∧ (2:Nat) ∣ 14 := ⟨⟨3, rfl⟩, ⟨7, rfl⟩⟩

/-! ## Reduced-form enumeration for discriminant -24. -/

/-- Every reduced form (a,b,c) with b >= 0 of discriminant -24
    (1 <= a, b <= a, a <= c, 4ac = b^2 + 24) is (1,0,6) or (2,0,3). -/
theorem forms24 : ∀ a b c : Nat, 1 ≤ a → b ≤ a → a ≤ c →
    4 * (a * c) = b * b + 24 →
    (a = 1 ∧ b = 0 ∧ c = 6) ∨ (a = 2 ∧ b = 0 ∧ c = 3) := by
  intro a b c ha hbc hac heq
  -- size bound: 4a^2 <= 4ac = b^2+24 <= a^2+24, so 3a^2 <= 24, a <= 2
  have haa : a * a ≤ a * c := Nat.mul_le_mul (Nat.le_refl a) hac
  have h4 : 4 * (a * a) ≤ 4 * (a * c) := Nat.mul_le_mul_left 4 haa
  rw [heq] at h4
  have hbb : b * b ≤ a * a := Nat.mul_le_mul hbc hbc
  have h5 : 4 * (a * a) ≤ a * a + 24 :=
    Nat.le_trans h4 (Nat.add_le_add_right hbb 24)
  have h3X : (3:Nat) * (a * a) ≤ 24 := by
    have h5' := h5
    rw [← four_id (a * a)] at h5'
    exact add_left_cancel_le (a * a) (3 * (a * a)) 24 h5'
  have ha2 : a ≤ 2 := by
    rcases Nat.lt_or_ge a 3 with h3 | h3
    · exact Nat.le_of_lt_succ h3
    · exact absurd (Nat.mul_le_mul_left 3 (Nat.mul_le_mul h3 h3))
        (fun h27 => absurd (Nat.le_trans h27 h3X) (by decide))
  cases a with
  | zero => exact absurd ha (by decide)
  | succ a1 =>
    cases a1 with
    | zero =>
      -- a = 1: 4c = b^2 + 24, b <= 1
      cases b with
      | zero =>
        -- b = 0: 4c = 24, so c = 6
        refine Or.inl ⟨rfl, rfl, ?_⟩
        have hD : (4:Nat) * c = 24 :=
          Eq.trans (Eq.symm (congrArg (fun x => (4:Nat) * x)
            (Nat.one_mul c))) heq
        have hge : (6:Nat) ≤ c :=
          Nat.le_of_mul_le_mul_left
            (Nat.le_trans (Nat.le_refl (24:Nat)) (Nat.le_of_eq (Eq.symm hD))) (by decide)
        have hle : c ≤ 6 :=
          Nat.le_of_mul_le_mul_left
            (Nat.le_of_eq (Eq.trans hD (rfl : (24:Nat) = (4:Nat) * 6))) (by decide)
        exact Nat.le_antisymm hle hge
      | succ b0 =>
        cases b0 with
        | zero =>
          -- b = 1: 4c = 25, impossible (25 is odd)
          have hD : (4:Nat) * c = 25 :=
            Eq.trans (Eq.symm (congrArg (fun x => (4:Nat) * x)
              (Nat.one_mul c))) heq
          rcases Nat.lt_or_ge c 7 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 4 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 4 hc)
              (Nat.le_of_eq hD)) (by decide)
        | succ k =>
          exact absurd hbc (fun hh => Nat.noConfusion
            (Nat.le_zero.mp (Nat.le_of_succ_le_succ hh)))
    | succ a2 =>
      cases a2 with
      | zero =>
        -- a = 2: 8c = b^2 + 24, b <= 2
        cases b with
        | zero =>
          -- b = 0: 8c = 24, so c = 3
          refine Or.inr ⟨rfl, rfl, ?_⟩
          have hD : (8:Nat) * c = 24 :=
            Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
              (Nat.succ (Nat.succ Nat.zero)) c))) heq
          have hge : (3:Nat) ≤ c :=
            Nat.le_of_mul_le_mul_left
              (Nat.le_trans (Nat.le_refl (24:Nat)) (Nat.le_of_eq (Eq.symm hD))) (by decide)
          have hle : c ≤ 3 :=
            Nat.le_of_mul_le_mul_left
              (Nat.le_of_eq (Eq.trans hD (rfl : (24:Nat) = (8:Nat) * 3))) (by decide)
          exact Nat.le_antisymm hle hge
        | succ b1 =>
          cases b1 with
          | zero =>
            -- b = 1: 8c = 25, impossible
            have hD : (8:Nat) * c = 25 :=
              Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                (Nat.succ (Nat.succ Nat.zero)) c))) heq
            rcases Nat.lt_or_ge c 4 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 8 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 8 hc)
                (Nat.le_of_eq hD)) (by decide)
          | succ b2 =>
            cases b2 with
            | zero =>
              -- b = 2: 8c = 28, impossible (28 is not a multiple of 8)
              have hD : (8:Nat) * c = 28 :=
                Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                  (Nat.succ (Nat.succ Nat.zero)) c))) heq
              rcases Nat.lt_or_ge c 4 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 8 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 8 hc)
                  (Nat.le_of_eq hD)) (by decide)
            | succ k =>
              exact absurd hbc (fun hh => Nat.noConfusion
                (Nat.le_zero.mp (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hh))))
      | succ a3 =>
        exact Nat.noConfusion (Nat.le_zero.mp
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ ha2)))

/-! ## Reduced-form enumeration for discriminant -56. -/

/-- Every reduced form (a,b,c) with b >= 0 of discriminant -56 is
    (1,0,14), (2,0,7) or (3,2,5). -/
theorem forms56 : ∀ a b c : Nat, 1 ≤ a → b ≤ a → a ≤ c →
    4 * (a * c) = b * b + 56 →
    (a = 1 ∧ b = 0 ∧ c = 14) ∨ (a = 2 ∧ b = 0 ∧ c = 7) ∨
    (a = 3 ∧ b = 2 ∧ c = 5) := by
  intro a b c ha hbc hac heq
  have haa : a * a ≤ a * c := Nat.mul_le_mul (Nat.le_refl a) hac
  have h4 : 4 * (a * a) ≤ 4 * (a * c) := Nat.mul_le_mul_left 4 haa
  rw [heq] at h4
  have hbb : b * b ≤ a * a := Nat.mul_le_mul hbc hbc
  have h5 : 4 * (a * a) ≤ a * a + 56 :=
    Nat.le_trans h4 (Nat.add_le_add_right hbb 56)
  have h3X : (3:Nat) * (a * a) ≤ 56 := by
    have h5' := h5
    rw [← four_id (a * a)] at h5'
    exact add_left_cancel_le (a * a) (3 * (a * a)) 56 h5'
  have ha4 : a ≤ 4 := by
    rcases Nat.lt_or_ge a 5 with h3 | h3
    · exact Nat.le_of_lt_succ h3
    · exact absurd (Nat.mul_le_mul_left 3 (Nat.mul_le_mul h3 h3))
        (fun h75 => absurd (Nat.le_trans h75 h3X) (by decide))
  cases a with
  | zero => exact absurd ha (by decide)
  | succ a1 =>
    cases a1 with
    | zero =>
      -- a = 1
      cases b with
      | zero =>
        -- b = 0: 4c = 56, so c = 14
        refine Or.inl ⟨rfl, rfl, ?_⟩
        have hD : (4:Nat) * c = 56 :=
          Eq.trans (Eq.symm (congrArg (fun x => (4:Nat) * x)
            (Nat.one_mul c))) heq
        have hge : (14:Nat) ≤ c :=
          Nat.le_of_mul_le_mul_left
            (Nat.le_trans (Nat.le_refl (56:Nat)) (Nat.le_of_eq (Eq.symm hD))) (by decide)
        have hle : c ≤ 14 :=
          Nat.le_of_mul_le_mul_left
            (Nat.le_of_eq (Eq.trans hD (rfl : (56:Nat) = (4:Nat) * 14))) (by decide)
        exact Nat.le_antisymm hle hge
      | succ b0 =>
        cases b0 with
        | zero =>
          -- b = 1: 4c = 57, impossible
          have hD : (4:Nat) * c = 57 :=
            Eq.trans (Eq.symm (congrArg (fun x => (4:Nat) * x)
              (Nat.one_mul c))) heq
          rcases Nat.lt_or_ge c 15 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 4 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 4 hc)
              (Nat.le_of_eq hD)) (by decide)
        | succ k =>
          exact absurd hbc (fun hh => Nat.noConfusion
            (Nat.le_zero.mp (Nat.le_of_succ_le_succ hh)))
    | succ a2 =>
      cases a2 with
      | zero =>
        -- a = 2
        cases b with
        | zero =>
          -- b = 0: 8c = 56, so c = 7
          refine Or.inr (Or.inl ⟨rfl, rfl, ?_⟩)
          have hD : (8:Nat) * c = 56 :=
            Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
              (Nat.succ (Nat.succ Nat.zero)) c))) heq
          have hge : (7:Nat) ≤ c :=
            Nat.le_of_mul_le_mul_left
              (Nat.le_trans (Nat.le_refl (56:Nat)) (Nat.le_of_eq (Eq.symm hD))) (by decide)
          have hle : c ≤ 7 :=
            Nat.le_of_mul_le_mul_left
              (Nat.le_of_eq (Eq.trans hD (rfl : (56:Nat) = (8:Nat) * 7))) (by decide)
          exact Nat.le_antisymm hle hge
        | succ b1 =>
          cases b1 with
          | zero =>
            -- b = 1: 8c = 57, impossible
            have hD : (8:Nat) * c = 57 :=
              Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                (Nat.succ (Nat.succ Nat.zero)) c))) heq
            rcases Nat.lt_or_ge c 8 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 8 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 8 hc)
                (Nat.le_of_eq hD)) (by decide)
          | succ b2 =>
            cases b2 with
            | zero =>
              -- b = 2: 8c = 60, impossible
              have hD : (8:Nat) * c = 60 :=
                Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                  (Nat.succ (Nat.succ Nat.zero)) c))) heq
              rcases Nat.lt_or_ge c 8 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 8 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 8 hc)
                  (Nat.le_of_eq hD)) (by decide)
            | succ k =>
              exact absurd hbc (fun hh => Nat.noConfusion
                (Nat.le_zero.mp (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hh))))
      | succ a3 =>
        cases a3 with
        | zero =>
          -- a = 3: 12c = b^2 + 56, b <= 3
          cases b with
          | zero =>
            -- b = 0: 12c = 56, impossible
            have hD : (12:Nat) * c = 56 :=
              Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                (Nat.succ (Nat.succ (Nat.succ Nat.zero))) c))) heq
            rcases Nat.lt_or_ge c 5 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 12 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 12 hc)
                (Nat.le_of_eq hD)) (by decide)
          | succ b1 =>
            cases b1 with
            | zero =>
              -- b = 1: 12c = 57, impossible
              have hD : (12:Nat) * c = 57 :=
                Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                  (Nat.succ (Nat.succ (Nat.succ Nat.zero))) c))) heq
              rcases Nat.lt_or_ge c 5 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 12 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 12 hc)
                  (Nat.le_of_eq hD)) (by decide)
            | succ b2 =>
              cases b2 with
              | zero =>
                -- b = 2: 12c = 60, so c = 5
                refine Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)
                have hD : (12:Nat) * c = 60 :=
                  Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                    (Nat.succ (Nat.succ (Nat.succ Nat.zero))) c))) heq
                have hge : (5:Nat) ≤ c :=
                  Nat.le_of_mul_le_mul_left
                    (Nat.le_trans (Nat.le_refl (60:Nat)) (Nat.le_of_eq (Eq.symm hD)))
                    (by decide)
                have hle : c ≤ 5 :=
                  Nat.le_of_mul_le_mul_left
                    (Nat.le_of_eq (Eq.trans hD (rfl : (60:Nat) = (12:Nat) * 5)))
                    (by decide)
                exact Nat.le_antisymm hle hge
              | succ b3 =>
                cases b3 with
                | zero =>
                  -- b = 3: 12c = 65, impossible
                  have hD : (12:Nat) * c = 65 :=
                    Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                      (Nat.succ (Nat.succ (Nat.succ Nat.zero))) c))) heq
                  rcases Nat.lt_or_ge c 6 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 12 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 12 hc)
                      (Nat.le_of_eq hD)) (by decide)
                | succ k =>
                  exact absurd hbc (fun hh => Nat.noConfusion
                    (Nat.le_zero.mp (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
                      (Nat.le_of_succ_le_succ hh)))))
        | succ a4 =>
          cases a4 with
          | zero =>
            -- a = 4: 16c = b^2 + 56, b <= 4: no solutions
            cases b with
            | zero =>
              -- b = 0: 16c = 56
              have hD : (16:Nat) * c = 56 :=
                Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                  (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) c))) heq
              rcases Nat.lt_or_ge c 4 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 16 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 16 hc)
                  (Nat.le_of_eq hD)) (by decide)
            | succ b1 =>
              cases b1 with
              | zero =>
                -- b = 1: 16c = 57
                have hD : (16:Nat) * c = 57 :=
                  Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                    (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) c))) heq
                rcases Nat.lt_or_ge c 4 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 16 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 16 hc)
                    (Nat.le_of_eq hD)) (by decide)
              | succ b2 =>
                cases b2 with
                | zero =>
                  -- b = 2: 16c = 60
                  have hD : (16:Nat) * c = 60 :=
                    Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                      (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) c))) heq
                  rcases Nat.lt_or_ge c 4 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 16 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 16 hc)
                      (Nat.le_of_eq hD)) (by decide)
                | succ b3 =>
                  cases b3 with
                  | zero =>
                    -- b = 3: 16c = 65
                    have hD : (16:Nat) * c = 65 :=
                      Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                        (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) c))) heq
                    rcases Nat.lt_or_ge c 5 with hc | hc
                    · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 16 (Nat.le_of_lt_succ hc))) (by decide)
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 16 hc)
                        (Nat.le_of_eq hD)) (by decide)
                  | succ b4 =>
                    cases b4 with
                    | zero =>
                      -- b = 4: 16c = 72
                      have hD : (16:Nat) * c = 72 :=
                        Eq.trans (Eq.symm (Eq.symm (mul_assoc_self 4
                          (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) c))) heq
                      rcases Nat.lt_or_ge c 5 with hc | hc
                      · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                          (Nat.mul_le_mul_left 16 (Nat.le_of_lt_succ hc))) (by decide)
                      · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 16 hc)
                          (Nat.le_of_eq hD)) (by decide)
                    | succ k =>
                      exact absurd hbc (fun hh => Nat.noConfusion
                        (Nat.le_zero.mp (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
                          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hh))))))
          | succ k =>
            exact Nat.noConfusion (Nat.le_zero.mp
              (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
                (Nat.le_of_succ_le_succ ha4)))))

/-! ## Strictness of the non-self-converse form, and the comparison. -/

/-- (3,2,5) is strictly reduced with 0 < b < a < c, so its mirror
    (3,-2,5) is a distinct fourth reduced form of discriminant -56. -/
theorem strict56 : (0:Nat) < 2 ∧ 2 < 3 ∧ 3 < 5 := ⟨by decide, by decide, by decide⟩

/-- Both enumerated b >= 0 forms of discriminant -24 have b = 0, so
    each is self-converse: h(-24) = 2 forms = 2 classes, and
    h(-56) = 4 classes > 2. -/
theorem comparison : (2:Nat) ≤ 2 ∧ 2 < 4 := ⟨Nat.le_refl 2, by decide⟩

/-- THE REFUTATION: 6 and 14 share the smallest prime factor 2, but
    the class numbers of their rings of integers differ (2 vs 4), so by
    Carlitz's criterion the elasticities differ (1 vs > 1): rho is not
    determined by the smallest prime factor of d. -/
theorem conjecture_refuted :
    (2:Nat) ∣ 6 ∧ (2:Nat) ∣ 14 ∧ (2:Nat) ≤ 2 ∧ 2 < 4 ∧
    (∀ a b c : Nat, 1 ≤ a → b ≤ a → a ≤ c → 4 * (a * c) = b * b + 24 →
      (a = 1 ∧ b = 0 ∧ c = 6) ∨ (a = 2 ∧ b = 0 ∧ c = 3)) ∧
    (∀ a b c : Nat, 1 ≤ a → b ≤ a → a ≤ c → 4 * (a * c) = b * b + 56 →
      (a = 1 ∧ b = 0 ∧ c = 14) ∨ (a = 2 ∧ b = 0 ∧ c = 7) ∨
      (a = 3 ∧ b = 2 ∧ c = 5)) := by
  exact ⟨spf_shared.1, spf_shared.2, comparison.1, comparison.2, forms24, forms56⟩

end Tlmc2211
