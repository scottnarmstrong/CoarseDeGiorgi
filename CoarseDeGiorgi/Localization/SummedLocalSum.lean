import CoarseDeGiorgi.Localization.SummedInequalities

/-! # Summing local bounds over a cover (abstract `ℝ≥0∞` form)

The local bounds `S z ≤ A * (∑' k, c k * T k z ^ (1/(2q))) * E z ^ (1/2)` are summed with
Minkowski's inequality in `k`, Hölder's inequality in `z` and bounded overlap. -/
namespace CoarseDeGiorgi.Localization
open scoped BigOperators ENNReal
noncomputable section

variable {ι : Type*}

theorem summed_local_bound (Z : Finset ι) (S E : ι → ℝ≥0∞) (T : ℕ → ι → ℝ≥0∞)
    (c B : ℕ → ℝ≥0∞) (A M Etot : ℝ≥0∞) {q r : ℝ} (hq : 1 < q) (hr : r = 2 * q / (q + 1))
    (hloc : ∀ z ∈ Z, S z ≤ A * (∑' k, c k * T k z ^ (1 / (2 * q))) * E z ^ (1 / 2 : ℝ))
    (hT : ∀ k, ∑ z ∈ Z, T k z ≤ M * B k) (hE : ∑ z ∈ Z, E z ≤ M * Etot) :
    (∑ z ∈ Z, S z ^ r) ^ (1 / r) ≤
      A * (M ^ (1 / (2 * q)) * M ^ (1 / 2 : ℝ)) *
        ((∑' k, c k * B k ^ (1 / (2 * q))) * Etot ^ (1 / 2 : ℝ)) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ (by positivity)]; linarith
  have h1q : (0 : ℝ) ≤ 1 / (2 * q) := by positivity
  set a : ℕ → ι → ℝ≥0∞ := fun k z => c k * (T k z ^ (1 / (2 * q)) * E z ^ (1 / 2 : ℝ)) with ha
  -- pointwise reduction
  have hS : ∀ z ∈ Z, S z ≤ A * ∑' k, a k z := by
    intro z hz
    refine (hloc z hz).trans (le_of_eq ?_)
    rw [mul_assoc, ← ENNReal.tsum_mul_right]
    congr 1
    refine tsum_congr fun k => ?_
    simp only [ha, mul_assoc]
  have step1 : (∑ z ∈ Z, S z ^ r) ^ (1 / r) ≤ (∑ z ∈ Z, (A * ∑' k, a k z) ^ r) ^ (1 / r) := by
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun z hz => ?_) (one_div_nonneg.mpr hr0.le)
    exact ENNReal.rpow_le_rpow (hS z hz) hr0.le
  have step2 : (∑ z ∈ Z, (A * ∑' k, a k z) ^ r) ^ (1 / r) =
      A * (∑ z ∈ Z, (∑' k, a k z) ^ r) ^ (1 / r) := by
    simp only [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
    rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr0.le),
      ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
  have step3 := minkowski_tsum Z a hr1
  have step4 : ∀ k, (∑ z ∈ Z, a k z ^ r) ^ (1 / r) ≤
      c k * ((M ^ (1 / (2 * q)) * M ^ (1 / 2 : ℝ)) * (B k ^ (1 / (2 * q)) * Etot ^ (1 / 2 : ℝ))) := by
    intro k
    have e1 : (∑ z ∈ Z, a k z ^ r) ^ (1 / r) =
        c k * (∑ z ∈ Z, (T k z ^ (1 / (2 * q)) * E z ^ (1 / 2 : ℝ)) ^ r) ^ (1 / r) := by
      simp only [ha, ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
      rw [← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr0.le),
        ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
    rw [e1]
    refine mul_le_mul_right ?_ _
    refine (holder_pair Z (T k) E hq hr).trans ?_
    have h2 := ENNReal.rpow_le_rpow (hT k) h1q
    have h3 := ENNReal.rpow_le_rpow hE (one_div_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2))
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1q] at h2
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h3
    calc _ ≤ (M ^ (1 / (2 * q)) * B k ^ (1 / (2 * q))) * (M ^ (1 / 2 : ℝ) * Etot ^ (1 / 2 : ℝ)) :=
          mul_le_mul' h2 h3
      _ = _ := by ring
  refine step1.trans (step2.le.trans ?_)
  refine mul_le_mul_right (step3.trans (ENNReal.tsum_le_tsum step4)) A |>.trans (le_of_eq ?_)
  rw [mul_assoc]
  congr 1
  have e : ∀ k, c k * ((M ^ (1 / (2 * q)) * M ^ (1 / 2 : ℝ)) *
      (B k ^ (1 / (2 * q)) * Etot ^ (1 / 2 : ℝ))) =
      ((M ^ (1 / (2 * q)) * M ^ (1 / 2 : ℝ)) * Etot ^ (1 / 2 : ℝ)) * (c k * B k ^ (1 / (2 * q))) := by
    intro k; ring
  rw [tsum_congr e, ENNReal.tsum_mul_left]
  ring

end
end CoarseDeGiorgi.Localization
