import CoarseDeGiorgi.Harnack.ReverseMoments.MomentConversion
import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas

open Homogenization MeasureTheory
open scoped ENNReal
namespace CoarseDeGiorgi.Harnack.Iterations

/-- The dyadic radii stay between the fixed inner and outer radii.
-/
theorem iteration_radius_bounds {ρ R : ℝ} (hρR : ρ < R) (j : ℕ) :
    ρ < ρ + (1 / 2 : ℝ) ^ j * (R - ρ) ∧
    ρ + (1 / 2 : ℝ) ^ j * (R - ρ) ≤ R := by
  have hpos : 0 < (1 / 2 : ℝ) ^ j := by positivity
  have hle : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor
  · linarith [mul_pos hpos (sub_pos.mpr hρR)]
  · nlinarith

/-- Exact logarithmic dyadic gap identity.
-/
theorem iteration_radius_log_gap {ρ R : ℝ} (hρR : ρ < R) (j : ℕ) :
    Real.log (1 / ((ρ + (1 / 2 : ℝ) ^ j * (R - ρ)) -
      (ρ + (1 / 2 : ℝ) ^ (j + 1) * (R - ρ)))) =
      Real.log (1 / (R - ρ)) + ((j : ℝ) + 1) * Real.log 2 := by
  have hgap : (ρ + (1 / 2 : ℝ) ^ j * (R - ρ)) -
      (ρ + (1 / 2 : ℝ) ^ (j + 1) * (R - ρ)) =
      (1 / 2 : ℝ) ^ (j + 1) * (R - ρ) := by rw [pow_succ]; ring
  rw [hgap]
  simp only [one_div, Real.log_inv]
  rw [Real.log_mul (by positivity) (sub_pos.mpr hρR).ne', Real.log_pow,
    Real.log_inv]
  push_cast
  ring

/-- For cubes with `1/2 ≤ ρ` and `R ≤ 1`, the normalized subset factor is at most `2^(d/b)`.
-/
theorem iteration_cube_subset_factor_le {d : ℕ} {ρ R b q : ℝ}
    (hρ : 1 / 2 ≤ ρ) (hR : R ≤ 1) (hb : 0 < b) (hbq : b ≤ q) :
    volume (originCube (d := d) ρ) ^ (-(1 / q)) *
      volume (originCube (d := d) R) ^ (1 / q) ≤
        ENNReal.ofReal ((2 : ℝ) ^ d) ^ (1 / b) := by
  have hρpos : 0 < ρ := by linarith
  have hq : 0 < q := hb.trans_le hbq
  have hinv : (volume (originCube (d := d) ρ))⁻¹ ≤ ENNReal.ofReal ((2 : ℝ) ^ d) := by
    rw [ReverseMoments.originCube_volume ρ hρpos.le,
      ← ENNReal.ofReal_inv_of_pos (pow_pos hρpos d)]
    apply ENNReal.ofReal_le_ofReal
    have hpow : (1 / 2 : ℝ) ^ d ≤ ρ ^ d := by gcongr
    have h := one_div_le_one_div_of_le (by positivity : 0 < (1 / 2 : ℝ) ^ d) hpow
    simpa only [one_div, inv_pow, inv_div, one_mul, inv_inv] using h
  have hD : 1 ≤ ENNReal.ofReal ((2 : ℝ) ^ d) := by
    simpa using ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  calc
    _ ≤ volume (originCube (d := d) ρ) ^ (-(1 / q)) * 1 :=
      mul_le_mul_of_nonneg_left
        (ENNReal.rpow_le_one (Scalar.volume_originCube_le_one hR) (by positivity)) zero_le
    _ = (volume (originCube (d := d) ρ))⁻¹ ^ (1 / q) := by
      rw [mul_one, ENNReal.rpow_neg, ENNReal.inv_rpow]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ d) ^ (1 / q) :=
      ENNReal.rpow_le_rpow hinv (by positivity)
    _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_le hD (one_div_le_one_div_of_le hb hbq)

/-- Every intermediate cube has volume at most 2^d times the inner cube volume.
-/
theorem iteration_cube_volume_le {d : ℕ} {ρ R : ℝ}
    (hρ : 1 / 2 ≤ ρ) (hR : R ≤ 1) :
    volume (originCube (d := d) R) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d) * volume (originCube (d := d) ρ) := by
  have hρpos : 0 < ρ := by linarith
  calc
    _ ≤ 1 := Scalar.volume_originCube_le_one hR
    _ ≤ _ := by
      rw [ReverseMoments.originCube_volume ρ hρpos.le,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ d)]
      have hpow : (1 / 2 : ℝ) ^ d ≤ ρ ^ d := by gcongr
      have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (2 : ℝ) ^ d)
      have heq : (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d = 1 := by rw [← mul_pow]; norm_num
      simpa only [heq, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hmul

end CoarseDeGiorgi.Harnack.Iterations
