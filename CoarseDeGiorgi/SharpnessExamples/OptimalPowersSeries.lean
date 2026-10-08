import CoarseDeGiorgi.SharpnessExamples.OptimalPowersCells
import CoarseDeGiorgi.SharpnessExamples.BesovCylinderSum
import CoarseDeGiorgi.Assembly.ClassicalMomentsSeries

/-! # The summed cylinder bound for the normalized half-power series of the moments

Step 3 of the proof of Proposition `p.sharpness.polynomial`: Minkowski (already in the level
bounds), square-root subadditivity, and the summed bound `e.sharpness.cylinder.discount`.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem op_three_pow_sq (k : ℕ) (b : ℝ) :
    Real.sqrt (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b))) = Real.rpow 3 (-((k : ℝ) * b)) := by
  rw [Real.sqrt_eq_rpow]
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul (by norm_num)]
  congr 1
  ring

private theorem op_fractions_eq {n k : ℕ} (epsilon v : ℝ) :
    finitePowerMean (fun η : SimplexIndex (n + 1) k =>
        cylinderResponseFraction (simplexCell k η) epsilon) v =
      cylinderFractionLevelMoment k (2 * epsilon) (0 : Vec n) v := by
  simp only [cylinderResponseFraction_eq_cylinderFraction]
  simp [finitePowerMean, cylinderFractionLevelMoment, SimplexIndex]

/-- The normalized half-power series of a sequence of levels dominated by `1 + c ×` the
cylinder fractions is at most `1 + (1 - 3^{-b}) √c · K ε^{ν/2}`. -/
theorem optimalPowers_series_bound {n : ℕ} {epsilon v b ν c : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) (hv : 1 ≤ v) (hb : 0 < b)
    (hνn : ν < n) (hνb : ν ≤ (n : ℝ) / v + 2 * b) (hc : 0 ≤ c)
    (u : ℕ → ℝ) (hu0 : ∀ k, 0 ≤ u k)
    (hu : ∀ k, Real.rpow (u k) (1 / v) ≤ 1 + c * finitePowerMean
      (fun η : SimplexIndex (n + 1) k => cylinderResponseFraction (simplexCell k η) epsilon) v) :
    ENNReal.ofReal (1 - Real.rpow 3 (-b)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) *
          (ENNReal.ofReal (u k)).rpow (1 / (2 * v)) ≤
      ENNReal.ofReal (1 + (1 - Real.rpow 3 (-b)) * Real.sqrt c *
        (cylinderRootConstant n v b ν * Real.rpow (2 * epsilon) (ν / 2))) := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hσ : Real.rpow 3 (-b) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hb)
  have hσ0 : 0 ≤ 1 - Real.rpow 3 (-b) := sub_nonneg.2 hσ.le
  obtain ⟨hsum, hbound⟩ := cylinderFractionDiscountedRoot_sum (n := n) (e := 2 * epsilon)
    (by linarith) (by linarith) (0 : Vec n) (fun i => by simp) hv hb hνn hνb
  set w : ℕ → ℝ := fun k => Real.rpow 3 (-((k : ℝ) * b)) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => Real.rpow_nonneg (by norm_num) _
  set M : ℕ → ℝ := fun k => cylinderFractionLevelMoment k (2 * epsilon) (0 : Vec n) v with hM
  have hM0 : ∀ k, 0 ≤ M k := fun k => by
    rw [hM]; dsimp only
    rw [← op_fractions_eq]
    exact finitePowerMean_nonneg _ (fun η =>
      (cylinderResponseFraction_bounds
        (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne
        epsilon).1) v
  set r : ℕ → ℝ := fun k => Real.sqrt (cylinderFractionDiscountedLevel k (2 * epsilon)
    (0 : Vec n) v b) with hr
  have hr_eq : ∀ k, r k = w k * Real.sqrt (M k) := by
    intro k
    simp only [hr, hw, hM, cylinderFractionDiscountedLevel]
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) from
      Real.rpow_nonneg (by norm_num) _), op_three_pow_sq]
  have hr0 : ∀ k, 0 ≤ r k := fun k => Real.sqrt_nonneg _
  -- the level bound
  have hlevel : ∀ k, w k * Real.rpow (u k) (1 / (2 * v)) ≤ w k + Real.sqrt c * r k := by
    intro k
    have h1 : Real.rpow (u k) (1 / (2 * v)) = Real.sqrt (Real.rpow (u k) (1 / v)) := by
      rw [Real.sqrt_eq_rpow]
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul (hu0 k)]
      congr 1
      field_simp
    have hMk := hu k
    rw [op_fractions_eq] at hMk
    have h2 : Real.sqrt (Real.rpow (u k) (1 / v)) ≤ 1 + Real.sqrt c * Real.sqrt (M k) := by
      refine (Real.sqrt_le_sqrt hMk).trans ?_
      rw [Real.sqrt_le_left (by positivity)]
      have := Real.sq_sqrt hc
      have := Real.sq_sqrt (hM0 k)
      nlinarith [Real.sqrt_nonneg c, Real.sqrt_nonneg (M k),
        mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg (M k))]
    rw [h1, hr_eq]
    calc w k * Real.sqrt (Real.rpow (u k) (1 / v))
        ≤ w k * (1 + Real.sqrt c * Real.sqrt (M k)) :=
          mul_le_mul_of_nonneg_left h2 (hw0 k)
      _ = _ := by ring
  have hrs : Summable r := hsum
  have hK0 : 0 ≤ cylinderRootConstant n v b ν * Real.rpow (2 * epsilon) (ν / 2) :=
    (tsum_nonneg hr0).trans hbound
  have hnorm := Assembly.ClassicalMomentsImpl.geometric_normalization hb
  have hterm : ∀ k, ENNReal.ofReal (w k) * (ENNReal.ofReal (u k)).rpow (1 / (2 * v)) ≤
      ENNReal.ofReal (w k) + ENNReal.ofReal (Real.sqrt c * r k) := by
    intro k
    have : ENNReal.ofReal (w k) * (ENNReal.ofReal (u k)).rpow (1 / (2 * v)) =
        ENNReal.ofReal (w k * Real.rpow (u k) (1 / (2 * v))) := by
      have e := ENNReal.ofReal_rpow_of_nonneg (hu0 k) (show 0 ≤ 1 / (2 * v) by positivity)
      rw [ENNReal.ofReal_mul (hw0 k)]
      exact congrArg _ e
    rw [this, ← ENNReal.ofReal_add (hw0 k) (mul_nonneg (Real.sqrt_nonneg _) (hr0 k))]
    exact ENNReal.ofReal_le_ofReal (hlevel k)
  have htsum : ∑' k : ℕ, ENNReal.ofReal (w k) * (ENNReal.ofReal (u k)).rpow (1 / (2 * v)) ≤
      ∑' k : ℕ, ENNReal.ofReal (w k) +
        ENNReal.ofReal (Real.sqrt c * ∑' k, r k) := by
    calc _ ≤ ∑' k : ℕ, (ENNReal.ofReal (w k) + ENNReal.ofReal (Real.sqrt c * r k)) :=
          ENNReal.tsum_le_tsum hterm
      _ = ∑' k : ℕ, ENNReal.ofReal (w k) + ∑' k : ℕ, ENNReal.ofReal (Real.sqrt c * r k) :=
          ENNReal.tsum_add
      _ = _ := by
          congr 1
          rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun k => mul_nonneg (Real.sqrt_nonneg _) (hr0 k)) (hrs.mul_left _), tsum_mul_left]
  calc _ ≤ ENNReal.ofReal (1 - Real.rpow 3 (-b)) *
        (∑' k : ℕ, ENNReal.ofReal (w k) + ENNReal.ofReal (Real.sqrt c * ∑' k, r k)) :=
        mul_le_mul_right htsum _
    _ = 1 + ENNReal.ofReal (1 - Real.rpow 3 (-b)) *
          ENNReal.ofReal (Real.sqrt c * ∑' k, r k) := by
        rw [mul_add]
        congr 1
    _ ≤ 1 + ENNReal.ofReal (1 - Real.rpow 3 (-b)) *
          ENNReal.ofReal (Real.sqrt c *
            (cylinderRootConstant n v b ν * Real.rpow (2 * epsilon) (ν / 2))) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul hσ0, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (mul_nonneg hσ0 (mul_nonneg (Real.sqrt_nonneg _) hK0))]
        congr 2
        ring

end

end CoarseDeGiorgi.SharpnessExamples
