module

public import CoarseDeGiorgi.SharpnessExamples.OptimalPowersSeries
public import CoarseDeGiorgi.SharpnessExamples.OptimalPowersField
public import CoarseDeGiorgi.CoefficientConditions.BesovSeries

/-! # Upper bounds for `Λ_ε` and `λ_ε^{-1}` from coefficient averages

Step 3 of the proof of Proposition `p.sharpness.polynomial`: `Λ_ε ≤ C ε^{-2θ}` and
`λ_ε^{-1} ≤ C` from the averages of the diagonal cylinder field over the simplices and the summed
cylinder bound.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem optimalPowers_rootConstant_nonneg (n : ℕ) {v b ν : ℝ} (hb : 0 < b) (hνn : ν < n) :
    0 ≤ cylinderRootConstant n v b ν := by
  unfold cylinderRootConstant
  have hγ : 0 < ((n : ℝ) - ν) / 2 := by linarith
  have h1 : 1 < Real.rpow 3 (((n : ℝ) - ν) / 2) := Real.one_lt_rpow (by norm_num) hγ
  have h2 : Real.rpow 3 (-b) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hb)
  have h3 : 0 < 1 - Real.rpow 3 (-b) := by linarith
  have h4 : 0 < Real.rpow 3 (((n : ℝ) - ν) / 2) - 1 := by linarith
  have h5 : 0 < Real.rpow 3 (((n : ℝ) - ν) / 2) := by linarith
  positivity

/-- The upper moment of a cylinder field. -/
theorem optimalPowers_upperMoment_cylinder_le {n : ℕ} {epsilon A b s p : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) (hA : 1 ≤ A) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hs : 0 < s) (hp : 1 ≤ p) (hν : 2 * s + (n : ℝ) / p < n)
    (ha : IsWeightedCoeffOn (originCube 1) (cylinderCoefficient (d := n + 1) epsilon A b)) :
    upperMoment (cylinderCoefficient epsilon A b) ha s p hs hp ≤
      ENNReal.ofReal ((1 + (1 - Real.rpow 3 (-s)) * Real.sqrt A *
        (cylinderRootConstant n p s (2 * s + (n : ℝ) / p) *
          Real.rpow (2 * epsilon) ((2 * s + (n : ℝ) / p) / 2))) ^ 2) := by
  have hX := optimalPowers_series_bound (n := n) (epsilon := epsilon) (v := p) (b := s)
    (ν := 2 * s + (n : ℝ) / p) (c := A) he he8 hp hs hν (by linarith) (by linarith)
    (fun k => upperCellAverage (cylinderCoefficient epsilon A b) ha k p)
    (fun k => div_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Nat.cast_nonneg _))
    (fun k => optimalPowers_upper_level k epsilon hA hb0 hb1 hp ha)
  unfold upperMoment
  have hy0 : 0 ≤ 1 + (1 - Real.rpow 3 (-s)) * Real.sqrt A *
        (cylinderRootConstant n p s (2 * s + (n : ℝ) / p) *
          Real.rpow (2 * epsilon) ((2 * s + (n : ℝ) / p) / 2)) := by
    have hσ : Real.rpow 3 (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
    have hK := optimalPowers_rootConstant_nonneg n (v := p) hs hν
    have : 0 ≤ Real.rpow (2 * epsilon) ((2 * s + (n : ℝ) / p) / 2) :=
      Real.rpow_nonneg (by linarith) _
    have h1 : 0 ≤ 1 - Real.rpow 3 (-s) := by linarith
    positivity
  rw [ENNReal.ofReal_pow hy0]
  exact pow_le_pow_left' hX 2

/-- The inverse of the lower moment of a cylinder field. -/
theorem optimalPowers_lowerMoment_inv_cylinder_le {n : ℕ} (hn : 1 ≤ n) {epsilon A b t q : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) (hA : 1 ≤ A) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (ht : 0 < t) (hq : 1 ≤ q) (hν : 2 * t + (n : ℝ) / q < n)
    (ha : IsWeightedCoeffOn (originCube 1) (cylinderCoefficient (d := n + 1) epsilon A b)) :
    (lowerMoment (cylinderCoefficient epsilon A b) ha t q ht hq)⁻¹ ≤
      ENNReal.ofReal ((1 + (1 - Real.rpow 3 (-t)) * Real.sqrt b⁻¹ *
        (cylinderRootConstant n q t (2 * t + (n : ℝ) / q) *
          Real.rpow (2 * epsilon) ((2 * t + (n : ℝ) / q) / 2))) ^ 2) := by
  have hX := optimalPowers_series_bound (n := n) (epsilon := epsilon) (v := q) (b := t)
    (ν := 2 * t + (n : ℝ) / q) (c := b⁻¹) he he8 hq ht hν (by linarith)
    (inv_nonneg.2 hb0.le)
    (fun k => lowerCellAverage (cylinderCoefficient epsilon A b) ha k q)
    (fun k => div_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Nat.cast_nonneg _))
    (fun k => optimalPowers_lower_level (by omega) k epsilon hA hb0 hb1 hq ha)
  rw [CoefficientConditions.lowerMoment_inv_eq]
  have hy0 : 0 ≤ 1 + (1 - Real.rpow 3 (-t)) * Real.sqrt b⁻¹ *
        (cylinderRootConstant n q t (2 * t + (n : ℝ) / q) *
          Real.rpow (2 * epsilon) ((2 * t + (n : ℝ) / q) / 2)) := by
    have hσ : Real.rpow 3 (-t) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht)
    have hK := optimalPowers_rootConstant_nonneg n (v := q) ht hν
    have : 0 ≤ Real.rpow (2 * epsilon) ((2 * t + (n : ℝ) / q) / 2) :=
      Real.rpow_nonneg (by linarith) _
    have h1 : 0 ≤ 1 - Real.rpow 3 (-t) := by linarith
    positivity
  rw [ENNReal.ofReal_pow hy0]
  exact pow_le_pow_left' hX 2

end

end CoarseDeGiorgi.SharpnessExamples
