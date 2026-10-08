import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace CoarseDeGiorgi.Foundations.Iteration

noncomputable section

def dyadicGap (δ : ℝ) (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n * (δ / 2)

theorem dyadicGap_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < dyadicGap δ n :=
  mul_pos (pow_pos (by norm_num) n) (half_pos hδ)

theorem dyadicGap_rpow {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) (n : ℕ) :
    (dyadicGap δ n) ^ (-γ) = ((2 : ℝ) ^ γ) ^ n * (δ / 2) ^ (-γ) := by
  rw [dyadicGap, Real.mul_rpow (pow_nonneg (by norm_num) n) (le_of_lt (half_pos hδ)),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Real.rpow_neg_eq_inv_rpow, one_div, inv_inv]

theorem dyadicGap_rpow_full {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) (n : ℕ) :
    (dyadicGap δ n) ^ (-γ) = ((2 : ℝ) ^ γ) ^ (n + 1) * δ ^ (-γ) := by
  have hg : dyadicGap δ n = (1 / 2 : ℝ) ^ (n + 1) * δ := by
    simp only [dyadicGap, pow_succ]
    ring
  rw [hg, Real.mul_rpow (pow_nonneg (by norm_num) _) hδ.le,
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Real.rpow_neg_eq_inv_rpow, one_div, inv_inv]

def holeRadius (ρ R : ℝ) (n : ℕ) : ℝ := R - (1 / 2 : ℝ) ^ n * (R - ρ)

theorem holeRadius_zero (ρ R : ℝ) : holeRadius ρ R 0 = ρ := by
  simp only [holeRadius, pow_zero, one_mul]
  ring

theorem holeRadius_gap (ρ R : ℝ) (n : ℕ) :
    holeRadius ρ R (n + 1) - holeRadius ρ R n = dyadicGap (R - ρ) n := by
  simp only [holeRadius, dyadicGap, pow_succ]
  ring

theorem holeRadius_bounds {ρ R : ℝ} (h : ρ < R) (n : ℕ) :
    ρ ≤ holeRadius ρ R n ∧ holeRadius ρ R n < R := by
  have hp : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hle : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  dsimp [holeRadius]
  constructor <;> nlinarith only [hp, hle, h]

end

end CoarseDeGiorgi.Foundations.Iteration
