import CoarseDeGiorgi.Harnack.Iterations.NormalizedMomentOrder
import Mathlib.Tactic

/-! Hölder restriction of a crossover bound to smaller positive exponents. -/

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Final

private theorem normalizedLpMoment_pow {d : ℕ} (V : Set (Vec d))
    (f : Vec d → ℝ) {b : ℝ} (hb : 0 < b) :
    (normalizedLpMoment b hb V f) ^ b =
      (volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |f x|) ^ b := by
  unfold normalizedLpMoment
  simp only [ENNReal.rpow_eq_pow]
  rw [← ENNReal.rpow_mul]
  rw [one_div_mul_cancel hb.ne', ENNReal.rpow_one]

/-- Hölder bounds the crossover product at a smaller exponent by the original
constant, enlarged to at least one. The constant is independent of the functions. -/
theorem crossover_product_le_of_exponent_le {d : ℕ}
    (V : Set (Vec d)) (f g : Vec d → ℝ) {b B : ℝ}
    (hb : 0 < b) (hbB : b ≤ B)
    (hf : AEStronglyMeasurable f (volume.restrict V))
    (hg : AEStronglyMeasurable g (volume.restrict V))
    (hVpos : 0 < volume V) (hVtop : volume V ≠ ⊤)
    {C : ℝ≥0∞}
    (hbound : ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |f x|) ^ B) *
      ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |g x|) ^ B) ≤ C) :
    ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |f x|) ^ b) *
      ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |g x|) ^ b) ≤ max C 1 := by
  have hB : 0 < B := hb.trans_le hbB
  have hfmono := Harnack.Iterations.normalizedLpMoment_mono V f hb hbB hf hVpos hVtop
  have hgmono := Harnack.Iterations.normalizedLpMoment_mono V g hb hbB hg hVpos hVtop
  have hprod := mul_le_mul' hfmono hgmono
  have hlarge :
      (normalizedLpMoment B hB V f * normalizedLpMoment B hB V g) ^ B ≤ C := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hB.le,
      normalizedLpMoment_pow V f hB, normalizedLpMoment_pow V g hB]
    exact hbound
  calc
    _ = (normalizedLpMoment b hb V f * normalizedLpMoment b hb V g) ^ b := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hb.le,
        normalizedLpMoment_pow V f hb, normalizedLpMoment_pow V g hb]
    _ ≤ (normalizedLpMoment B hB V f * normalizedLpMoment B hB V g) ^ b :=
      ENNReal.rpow_le_rpow hprod hb.le
    _ = ((normalizedLpMoment B hB V f * normalizedLpMoment B hB V g) ^ B) ^ (b / B) := by
      rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hB.ne']
    _ ≤ (max C 1) ^ (b / B) :=
      ENNReal.rpow_le_rpow (hlarge.trans (le_max_left _ _)) (div_nonneg hb.le hB.le)
    _ ≤ max C 1 := by
      have hratio : b / B ≤ 1 := (div_le_one hB).mpr hbB
      simpa only [ENNReal.rpow_one] using
        (ENNReal.rpow_le_rpow_of_exponent_le (le_max_right C 1) hratio)

/-- Restrict a crossover bound for a positive function and its reciprocal. -/
theorem crossover_signed_product_le_of_exponent_le {d : ℕ}
    (V : Set (Vec d)) (f : Vec d → ℝ) {b B : ℝ}
    (hb : 0 < b) (hbB : b ≤ B)
    (hf : AEStronglyMeasurable f (volume.restrict V))
    (hfpos : ∀ᵐ x ∂(volume.restrict V), 0 < f x)
    (hVpos : 0 < volume V) (hVtop : volume V ≠ ⊤)
    {C : ℝ≥0∞}
    (hbound : ((volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x ^ B)) *
      ((volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x ^ (-B))) ≤ C) :
    ((volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x ^ b)) *
      ((volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x ^ (-b))) ≤ max C 1 := by
  have hplus (β : ℝ) :
      (∫⁻ x in V, ENNReal.ofReal (f x ^ β)) =
        ∫⁻ x in V, (ENNReal.ofReal |f x|) ^ β := by
    apply lintegral_congr_ae
    filter_upwards [hfpos] with x hx
    rw [abs_of_pos hx, ENNReal.ofReal_rpow_of_pos hx]
  have hminus (β : ℝ) :
      (∫⁻ x in V, ENNReal.ofReal (f x ^ (-β))) =
        ∫⁻ x in V, (ENNReal.ofReal |(f x)⁻¹|) ^ β := by
    apply lintegral_congr_ae
    filter_upwards [hfpos] with x hx
    rw [abs_of_pos (inv_pos.mpr hx)]
    calc
      _ = ENNReal.ofReal ((f x)⁻¹ ^ β) := by
        rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le]
      _ = _ := (ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hx)).symm
  rw [hplus B, hminus B] at hbound
  rw [hplus b, hminus b]
  exact crossover_product_le_of_exponent_le V f (fun x => (f x)⁻¹) hb hbB hf
    hf.aemeasurable.inv.aestronglyMeasurable hVpos hVtop hbound

end CoarseDeGiorgi.Harnack.Final
