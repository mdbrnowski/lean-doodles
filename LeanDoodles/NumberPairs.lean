/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic


/-- Returns sum of digits of a natural number. -/
def digitSum (n : ℕ) : ℕ :=
  if n = 0 then 0 else n % 10 + digitSum (n / 10)


lemma digitSum_n_eq_digitSum_10n (n : ℕ) : digitSum n = digitSum (10 * n) := by
  unfold digitSum
  by_cases h : n = 0
  · simp [h]
  · nth_rw 2 [digitSum]
    simp [h]


lemma n_ModEq9_digitSum_n (n : ℕ) : n ≡ digitSum n [MOD 9] := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases lt_or_ge n 10 with h_lt | h_ge
    -- Base case: n < 10
    · unfold digitSum
      split_ifs with n_eq_0
      · simp [n_eq_0]
        rfl
      · rw [Nat.mod_eq_of_lt h_lt, Nat.div_eq_of_lt h_lt]
        simp [digitSum]
        rfl
    -- Inductive step: n ≥ 10
    · set d := n / 10
      set r := n % 10
      have h_decomp : n = 10 * d + r := by omega
      have d_lt_n : d < n := by omega
      have IH_d : d ≡ digitSum d [MOD 9] := ih d d_lt_n
      unfold digitSum
      have n_ne_0 : n ≠ 0 := by omega
      simp [n_ne_0]
      have h10 : 10 ≡ 1 [MOD 9] := by decide
      nth_rw 1 [h_decomp]
      calc
        10 * d + r ≡ 1 * d + r [MOD 9] := by gcongr
        _ = r + d := by omega
        _ ≡ r + digitSum d [MOD 9] := by gcongr


theorem NumberPair_exist_iff_9_dvd_d (d : ℕ) :
    (∃ a b : ℕ, b - a = d ∧ digitSum a = digitSum b) ↔ (9 ∣ d) := by
  constructor
  · intro h
    rcases h with ⟨a, b, h₁, h₂⟩
    have a_ModEq9_b : a ≡ b [MOD 9] := by
      calc
        a ≡ digitSum a [MOD 9] := n_ModEq9_digitSum_n a
        _ = digitSum b := h₂
        _ ≡ b [MOD 9] := (n_ModEq9_digitSum_n b).symm
    by_cases a_le_b : a ≤ b
    · have b_eq_d_add_a : b = d + a := (Nat.sub_eq_iff_eq_add a_le_b).mp h₁
      have d_ModEq9_zero : d ≡ 0 [MOD 9] := by
        rw [← Nat.zero_add a, b_eq_d_add_a] at a_ModEq9_b
        exact (Nat.ModEq.add_right_cancel' a a_ModEq9_b).symm
      exact Nat.modEq_zero_iff_dvd.mp d_ModEq9_zero
    · omega -- a > b → d = b - a = 0
  · intro h
    use d / 9
    use 10 * (d / 9)
    constructor
    · omega
    · exact digitSum_n_eq_digitSum_10n (d / 9)
