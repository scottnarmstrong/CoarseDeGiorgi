import CoarseDeGiorgi.Foundations.Reconstruction.Defs
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod

/-! # The two-integral kernel bound in nonnegative form -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Hölder against the constant function, without dividing by the measure mass. -/
theorem lintegral_rpow_le_mass_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {g : X → ℝ≥0∞} (hg : AEMeasurable g μ) {r : ℝ} (hr : 1 < r) :
    (∫⁻ x, g x ∂μ) ^ r ≤ (μ Set.univ) ^ (r - 1) * ∫⁻ x, g x ^ r ∂μ := by
  have hp := Real.HolderConjugate.conjExponent hr
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp hg aemeasurable_const
    (g := fun _ => (1 : ℝ≥0∞))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one] at hh
  have hpow := ENNReal.rpow_le_rpow hh (by linarith : 0 ≤ r)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ r),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hpow
  have hrr : (1 / r) * r = 1 := by field_simp
  have hqr : (1 / r.conjExponent) * r = r - 1 := by
    rw [Real.conjExponent]
    field_simp
  rw [hrr, hqr, ENNReal.rpow_one] at hpow
  rw [mul_comm] at hpow
  exact hpow

/-- Weighted Hölder, including kernels of mass zero. -/
theorem lintegral_weighted_rpow_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {H g : X → ℝ≥0∞} (hH : Measurable H) (hg : Measurable g)
    {r : ℝ} (hr : 1 < r) :
    (∫⁻ y, H y * g y ∂μ) ^ r ≤
      (∫⁻ y, H y ∂μ) ^ (r - 1) * ∫⁻ y, H y * g y ^ r ∂μ := by
  have h := lintegral_rpow_le_mass_mul (μ.withDensity H) hg.aemeasurable hr
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_withDensity_eq_lintegral_mul _ hH hg,
    lintegral_withDensity_eq_lintegral_mul _ hH (hg.pow_const r)] at h
  exact h

/-- Both integral bounds give the Lʳ bound for a nonnegative kernel operator. -/
theorem lintegral_schur_rpow_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (H : X → Y → ℝ≥0∞) (g : Y → ℝ≥0∞)
    (hH : Measurable (Function.uncurry H)) (hg : Measurable g)
    {M : ℝ≥0∞} (hrow : ∀ x, ∫⁻ y, H x y ∂ν ≤ M)
    (hcol : ∀ y, ∫⁻ x, H x y ∂μ ≤ M) {r : ℝ} (hr : 1 < r) :
    ∫⁻ x, (∫⁻ y, H x y * g y ∂ν) ^ r ∂μ ≤ M ^ r * ∫⁻ y, g y ^ r ∂ν := by
  have hprod : Measurable (fun p : X × Y => H p.1 p.2 * g p.2 ^ r) :=
    hH.mul ((hg.comp measurable_snd).pow_const r)
  calc
    _ ≤ ∫⁻ x, M ^ (r - 1) * ∫⁻ y, H x y * g y ^ r ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      exact (lintegral_weighted_rpow_le ν (hH.comp (measurable_const.prodMk measurable_id)) hg hr).trans
        (mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hrow x) (by linarith)) bot_le)
    _ = M ^ (r - 1) * ∫⁻ x, ∫⁻ y, H x y * g y ^ r ∂ν ∂μ :=
      lintegral_const_mul _ hprod.lintegral_prod_right
    _ = M ^ (r - 1) * ∫⁻ y, (∫⁻ x, H x y ∂μ) * g y ^ r ∂ν := by
      rw [lintegral_lintegral_swap hprod.aemeasurable]
      congr 1
      apply lintegral_congr
      intro y
      exact lintegral_mul_const _ (hH.comp (measurable_id.prodMk measurable_const))
    _ ≤ M ^ (r - 1) * ∫⁻ y, M * g y ^ r ∂ν := by
      apply mul_le_mul_of_nonneg_left (lintegral_mono fun y =>
        mul_le_mul_of_nonneg_right (hcol y) bot_le) bot_le
    _ = M ^ r * ∫⁻ y, g y ^ r ∂ν := by
      rw [lintegral_const_mul _ (hg.pow_const r), ← mul_assoc]
      have hpow : M ^ (r - 1) * M = M ^ r := by
        calc
          _ = M ^ (r - 1) * M ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
          _ = M ^ (r - 1 + 1) :=
            (ENNReal.rpow_add_of_nonneg (r - 1) 1 (by linarith) (by norm_num)).symm
          _ = _ := by congr 1; ring
      rw [hpow]

end

end CoarseDeGiorgi.Foundations.Reconstruction
