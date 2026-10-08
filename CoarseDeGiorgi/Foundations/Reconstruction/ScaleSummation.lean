module

public import CoarseDeGiorgi.Foundations.Reconstruction.Defs
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Nonnegative geometric summation for reconstruction tails -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open scoped BigOperators ENNReal

noncomputable section

/-- Reversed finite geometric sums have the same bound as forward geometric sums. -/
theorem sum_geometric_reverse_le (θ : ℝ≥0∞) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), θ ^ (k - j) ≤ (1 - θ)⁻¹ := by
  have heq : (∑ j ∈ Finset.range (k + 1), θ ^ (k - j)) =
      ∑ j ∈ Finset.range (k + 1), θ ^ j := by
    simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun j => θ ^ j) (k + 1)
  rw [heq, ← ENNReal.tsum_geometric]
  exact ENNReal.sum_le_tsum _

/-- Tonelli and one geometric sum collapse the triangular tail convolution. -/
theorem tsum_geometric_tails_le (θ : ℝ≥0∞) (a : ℕ → ℝ≥0∞) :
    (∑' j : ℕ, ∑' k : ℕ, if j ≤ k then θ ^ (k - j) * a k else 0) ≤
      (1 - θ)⁻¹ * ∑' k : ℕ, a k := by
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  have heq : (∑' j : ℕ, if j ≤ k then θ ^ (k - j) * a k else 0) =
      ∑ j ∈ Finset.range (k + 1), θ ^ (k - j) * a k := by
    rw [tsum_eq_sum (s := Finset.range (k + 1)) (fun j hj => by
      have hn : ¬j ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      simp only [hn, ite_false])]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  rw [heq, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_geometric_reverse_le θ k) bot_le

/-- The geometric multiplier is finite in the fractional range. -/
theorem geometric_tail_constant_ne_top {θ : ℝ≥0∞} (hθ : θ < 1) :
    (1 - θ)⁻¹ ≠ ∞ := by
  apply ENNReal.inv_ne_top.mpr
  exact ne_of_gt (tsub_pos_iff_lt.mpr hθ)

end

end CoarseDeGiorgi.Foundations.Reconstruction
