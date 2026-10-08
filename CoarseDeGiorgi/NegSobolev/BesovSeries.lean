import CoarseDeGiorgi.Statements.GaussianKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Passing from level estimates to the half-power Besov series

All sums take values in `ℝ≥0∞`, so the comparison does not require a separate
summability hypothesis and applies also to divergent series.
-/

open scoped ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- A termwise comparison survives multiplication by arbitrary nonnegative weights
and summation after taking square roots. -/
theorem half_series_le_of_le (C : ℝ≥0∞) (A B w : ℕ → ℝ≥0∞)
    (h : ∀ k, A k ≤ C * B k) :
    (∑' k, w k * (A k) ^ (1 / 2 : ℝ)) ≤
      C ^ (1 / 2 : ℝ) * ∑' k, w k * (B k) ^ (1 / 2 : ℝ) := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  have hk := ENNReal.rpow_le_rpow (h k) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hk
  calc
    _ ≤ w k * (C ^ (1 / 2 : ℝ) * (B k) ^ (1 / 2 : ℝ)) := mul_le_mul_right hk _
    _ = _ := by ac_rfl

/-- The "Consequently" step in `p.besov.averages`, for an arbitrary family of arithmetic means.
Its hypotheses are precisely the two level comparisons; the source theorem must
establish those comparisons before applying this algebraic lemma. -/
theorem besov_series_comparison_of_levels (C : ℝ) (hC : 0 < C)
    (p : ℝ) (mean heat w : ℕ → ℝ≥0∞)
    (hlower : ∀ k, ENNReal.ofReal C⁻¹ * (mean k) ^ (1 / p) ≤ heat k)
    (hupper : ∀ k, heat k ≤ ENNReal.ofReal C * (mean k) ^ (1 / p)) :
    ((∑' k, w k * (mean k) ^ (1 / (2 * p))) ≤
        ENNReal.ofReal (Real.sqrt C) * ∑' k, w k * (heat k) ^ (1 / 2 : ℝ)) ∧
      ((∑' k, w k * (heat k) ^ (1 / 2 : ℝ)) ≤
        ENNReal.ofReal (Real.sqrt C) * ∑' k, w k * (mean k) ^ (1 / (2 * p))) := by
  have hroot : (ENNReal.ofReal C) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt C) := by
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_pos hC]
  have hhalf (k : ℕ) : ((mean k) ^ (1 / p)) ^ (1 / 2 : ℝ) =
      (mean k) ^ (1 / (2 * p)) := by
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hlower' (k : ℕ) : (mean k) ^ (1 / p) ≤ ENNReal.ofReal C * heat k := by
    have h := mul_le_mul_right (hlower k) (ENNReal.ofReal C)
    rw [← mul_assoc, ← ENNReal.ofReal_mul hC.le, mul_inv_cancel₀ hC.ne',
      ENNReal.ofReal_one, one_mul] at h
    exact h
  constructor
  · have h := half_series_le_of_le (ENNReal.ofReal C) (fun k => (mean k) ^ (1 / p))
      heat w hlower'
    simpa only [hroot, hhalf] using h
  · have h := half_series_le_of_le (ENNReal.ofReal C) heat (fun k => (mean k) ^ (1 / p))
      w hupper
    simpa only [hroot, hhalf] using h

end CoarseDeGiorgi.NegSobolev
