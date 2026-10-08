import CoarseDeGiorgi.SharpnessExamples.BesovGeometricSum
import CoarseDeGiorgi.SharpnessExamples.CylinderAveragesDiscounted

/-! # The summed cylinder averages over simplex levels

The summed bound `e.sharpness.cylinder.discount` for the discounted levels of the cylinder fractions
in the simplex triangulations.
-/

open Homogenization MeasureTheory
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

/-- The constant in the summed bound. -/
noncomputable def cylinderRootConstant (n : ℕ) (v b ν : ℝ) : ℝ :=
  Real.sqrt (cylinderFractionDiscountedUpperConstant n v) *
    (Real.rpow 3 (((n : ℝ) - ν) / 2) / (Real.rpow 3 (((n : ℝ) - ν) / 2) - 1) +
      1 / (1 - Real.rpow 3 (-b)))

/-- Summed bound `e.sharpness.cylinder.discount` for the simplex levels of the fractions of a
cylinder. -/
theorem cylinderFractionDiscountedRoot_sum {n : ℕ} {e : ℝ} (he : 0 < e) (he4 : e < 1 / 4)
    (center : Vec n) (hcenter : ∀ i, |center i| ≤ 1 / 4) {v b ν : ℝ} (hv : 1 ≤ v)
    (hb : 0 < b) (hνn : ν < n) (hνb : ν ≤ (n : ℝ) / v + 2 * b) :
    Summable (fun k => Real.sqrt (cylinderFractionDiscountedLevel k e center v b)) ∧
      ∑' k, Real.sqrt (cylinderFractionDiscountedLevel k e center v b) ≤
        cylinderRootConstant n v b ν * Real.rpow e (ν / 2) := by
  have he1 : e < 1 := he4.trans (by norm_num)
  obtain ⟨hs, hsum⟩ := discountedRoot_sum n he he1 hv hb hνn hνb
  have hC : 0 ≤ cylinderFractionDiscountedUpperConstant n v := by
    unfold cylinderFractionDiscountedUpperConstant
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _)
  have hterm : ∀ k, Real.sqrt (cylinderFractionDiscountedLevel k e center v b) ≤
      Real.sqrt (cylinderFractionDiscountedUpperConstant n v) * discountedRoot n v b e k := by
    intro k
    unfold discountedRoot
    rw [← Real.sqrt_mul hC]
    apply Real.sqrt_le_sqrt
    have hmoment := cylinderFraction_level_moment_upper he he4 center hcenter v hv k
    have hw : 0 ≤ Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) := Real.rpow_nonneg (by norm_num) _
    unfold cylinderFractionDiscountedLevel
    calc _ ≤ Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
          (cylinderFractionDiscountedUpperConstant n v * cylinderPhi n v e k) :=
        mul_le_mul_of_nonneg_left hmoment hw
      _ = _ := by unfold cylinderFractionDiscountedUpperConstant; ring
  have hsumm : Summable (fun k => Real.sqrt (cylinderFractionDiscountedLevel k e center v b)) :=
    Summable.of_nonneg_of_le (fun k => Real.sqrt_nonneg _) hterm (hs.mul_left _)
  refine ⟨hsumm, ?_⟩
  calc _ ≤ ∑' k, Real.sqrt (cylinderFractionDiscountedUpperConstant n v) *
        discountedRoot n v b e k := hsumm.tsum_le_tsum hterm (hs.mul_left _)
    _ = Real.sqrt (cylinderFractionDiscountedUpperConstant n v) *
        ∑' k, discountedRoot n v b e k := tsum_mul_left
    _ ≤ Real.sqrt (cylinderFractionDiscountedUpperConstant n v) *
        ((Real.rpow 3 (((n : ℝ) - ν) / 2) / (Real.rpow 3 (((n : ℝ) - ν) / 2) - 1) +
          1 / (1 - Real.rpow 3 (-b))) * Real.rpow e (ν / 2)) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = _ := by unfold cylinderRootConstant; ring

end CoarseDeGiorgi.SharpnessExamples
