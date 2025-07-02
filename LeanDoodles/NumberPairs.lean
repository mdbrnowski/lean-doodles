import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic


/-- Returns sum of digits of a natural number. -/
def digitSum (n : ℕ) : ℕ :=
  if n = 0 then 0 else n % 10 + digitSum (n / 10)


lemma s_n_eq_s_10n : ∀ n : ℕ, digitSum n = digitSum (10 * n) := by
  intro n
  rw [digitSum]
  nth_rw 2 [digitSum]
  by_cases h : n = 0
  · simp [h]
  . nth_rw 2 [digitSum]
    simp [h]


lemma n_congruent_digitSum_n_mod_9 (n : ℕ) : n ≡ digitSum n [MOD 9] := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases' lt_or_ge n 10 with h_lt h_ge
    -- Base case: n < 10
    rw [digitSum]
    by_cases n_eq_0 : n = 0
    case pos =>
      simp [n_eq_0]
      rfl
    case neg =>
      simp [n_eq_0]
      rw [Nat.mod_eq_of_lt h_lt]
      rw [Nat.div_eq_of_lt h_lt]
      simp [digitSum]
      rfl
    -- Inductive step: n ≥ 10
    set d := n / 10
    set r := n % 10
    have h_decomp : n = 10 * d + r := by
      rw [Nat.div_add_mod _ 10]
    have d_lt_n : d < n := by
      rw [h_decomp]
      have d_pos : 0 < d := by
        apply Nat.div_pos h_ge
        decide
      have d_lt_10d : d < 10 * d := by
        nth_rw 1 [← Nat.mul_one d]
        nth_rw 2 [Nat.mul_comm]
        apply (Nat.mul_lt_mul_left d_pos).mpr
        decide
      exact Nat.lt_add_right r d_lt_10d
    have IH_d : d ≡ digitSum d [MOD 9] := ih d d_lt_n
    rw [digitSum]
    have n_ne_0 : n ≠ 0 := by
      intro h
      rw [h] at h_ge
      contradiction
    simp [n_ne_0]
    have h10 : 10 ≡ 1 [MOD 9] := by decide
    nth_rw 1 [h_decomp]
    calc
      10 * d + r ≡ 1 * d + r [MOD 9] := by
        apply Nat.ModEq.add_right
        apply Nat.ModEq.mul_right _ h10
      _ = d + r := by rw [Nat.one_mul]
      _ = r + d := by rw [Nat.add_comm]
      _ ≡ r + digitSum d [MOD 9] := Nat.ModEq.add_left r IH_d
