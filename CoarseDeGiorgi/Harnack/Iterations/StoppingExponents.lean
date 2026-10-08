module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Iterations

/-- A geometric exponent sequence crosses every larger positive target. The
first crossing has a one-step overshoot bounded by `χ`.
-/
theorem exists_geometric_first_crossing {χ a b : ℝ}
    (hχ : 1 < χ) (ha : 0 < a) (hab : a < b) :
    ∃ N : ℕ, 0 < N ∧ b ≤ a * χ ^ N ∧ a * χ ^ N < χ * b ∧
      ∀ j < N, a * χ ^ j < b := by
  have hchi0 : 0 ≤ χ := le_trans (by norm_num) hχ.le
  have hchiPos : 0 < χ := lt_trans zero_lt_one hχ
  have hpow (n : ℕ) : 1 + (n : ℝ) * (χ - 1) ≤ χ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have hmul := mul_le_mul_of_nonneg_right ih hchi0
      have herror : 0 ≤ (n : ℝ) * (χ - 1) ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg (χ - 1))
      have hncast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      rw [hncast]
      nlinarith
  have hk : 0 < χ - 1 := by linarith
  let B : ℝ := (b / a - 1) / (χ - 1)
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have hbound : b / a < 1 + (n : ℝ) * (χ - 1) := by
    dsimp [B] at hn
    rw [div_lt_iff₀ hk] at hn
    linarith
  have hmult : b < a * (1 + (n : ℝ) * (χ - 1)) := by
    have hmul : a * (b / a) < a * (1 + (n : ℝ) * (χ - 1)) :=
      mul_lt_mul_of_pos_left hbound ha
    calc
      b = a * (b / a) := by field_simp [ne_of_gt ha]
      _ < a * (1 + (n : ℝ) * (χ - 1)) := hmul
  have hex : ∃ n : ℕ, b ≤ a * χ ^ n := by
    refine ⟨n, ?_⟩
    have hpow' := mul_le_mul_of_nonneg_left (hpow n) ha.le
    exact le_of_lt (lt_of_lt_of_le hmult hpow')
  let N := Nat.find hex
  have hcross : b ≤ a * χ ^ N := Nat.find_spec hex
  have hminimal : ∀ j < N, a * χ ^ j < b := by
    intro j hj
    have hnot : ¬ b ≤ a * χ ^ j := by
      intro hge
      have hNle := Nat.find_min' hex hge
      omega
    exact lt_of_not_ge hnot
  have hNpos : 0 < N := by
    by_contra hn0
    have hN0 : N = 0 := by omega
    rw [hN0, pow_zero, mul_one] at hcross
    exact (not_le_of_gt hab) hcross
  have hprev : a * χ ^ (N - 1) < b := hminimal (N - 1) (by omega)
  have hpowstep : χ ^ N = χ ^ (N - 1) * χ := by
    calc
      χ ^ N = χ ^ ((N - 1) + 1) := by congr 1; omega
      _ = χ ^ (N - 1) * χ := by rw [pow_succ]
  have hover : a * χ ^ N < χ * b := by
    rw [hpowstep]
    nlinarith [mul_lt_mul_of_pos_right hprev hchiPos]
  exact ⟨N, hNpos, hcross, hover, hminimal⟩

end CoarseDeGiorgi.Harnack.Iterations
