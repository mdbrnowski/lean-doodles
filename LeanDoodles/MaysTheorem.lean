/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Michał Dobranowski
-/
import Mathlib.Tactic

/-- Result of the social choice function. -/
inductive Result where
  | A
  | B
  | tie
  deriving DecidableEq, Repr

/-- Majority rule: the candidate who received more votes wins. -/
def majority_rule (a b : ℕ) : Result :=
  if a = b then Result.tie
  else if a > b then Result.A
  else Result.B

/-- Social choice function is near decisive if it chooses exactly one winner in every situation
except when both candidates receive the same number of votes. -/
def near_decisiveness (f : ℕ → ℕ → Result) : Prop :=
  ∀ a b, (f a b = Result.tie ↔ a = b)

/-- Social choice function is neutral if all candidates are treated equally. -/
def neutrality (f : ℕ → ℕ → Result) : Prop :=
  ∀ a b, (f a b = Result.A ↔ f b a = Result.B) ∧
         (f a b = Result.B ↔ f b a = Result.A)

/-- Social choice function is monotone if changing votes in favor of the winning candidate does not
change the result. -/
def monotonicity (f : ℕ → ℕ → Result) : Prop :=
  ∀ a b k, (f a b = Result.A → f (a + k) (b - k) = Result.A) ∧
           (f a b = Result.B → f (a - k) (b + k) = Result.B)

theorem mays_theorem (f : ℕ → ℕ → Result)
    (h : near_decisiveness f ∧ neutrality f ∧ monotonicity f) :
    f = majority_rule := by
  ext a b
  unfold majority_rule
  let ⟨h_decisive, h_neutral, h_monotone⟩ := h
  by_cases a_eq_b : a = b
  · rw [if_pos a_eq_b]
    exact (h_decisive a b).mpr a_eq_b
  · simp [a_eq_b]
    wlog b_lt_a : b < a generalizing a b
    · simp [b_lt_a]
      have this := this b a (a_eq_b ∘ Eq.symm)
      have a_lt_b : a < b := by omega
      simp [a_lt_b] at this
      exact (h_neutral a b).right.mpr this
    · simp [b_lt_a]
      have res_ne_tie : ¬f a b = Result.tie := by
        have := (h_decisive a b).mp
        contrapose! this
        trivial
      have res_ne_B : ¬f a b = Result.B := by
        by_contra res_eq_B
        by_cases even_sub : Even (a - b)
        · set k := (a - b) / 2 with hk
          have a'_eq_b' : a - k = b + k := by
            calc
              a - k = (a - b) + b - k := by omega
              _ = (2 * k) + b - k := by rw [hk, Nat.mul_comm, Nat.div_two_mul_two_of_even even_sub]
              _ = b + k := by omega
          have res'_eq_B := (h_monotone a b k).right res_eq_B
          have res'_eq_tie := (h_decisive (a - k) (b + k)).mpr a'_eq_b'
          rw [res'_eq_B] at res'_eq_tie
          contradiction
        · set l := (a - b) with hl
          have res'_eq_A := (h_neutral a b).right.mp res_eq_B
          have res_eq_A : f a b = Result.A := by
            have b_add_l_eq_a : b + l = a := by omega
            have a_sub_l_eq_b : a - l = b := by omega
            have := (h_monotone b a l).left res'_eq_A
            rwa [b_add_l_eq_a, a_sub_l_eq_b] at this
          rw [res_eq_B] at res_eq_A
          contradiction
      cases res : f a b <;> trivial
