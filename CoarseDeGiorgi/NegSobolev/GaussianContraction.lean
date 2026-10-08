import CoarseDeGiorgi.NegSobolev.GaussianBasic
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Normalized Gaussian averaging and integral power bounds -/

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- The nonnegative Gaussian has Lebesgue integral one. -/
theorem lintegral_gaussianKernel {d : ℕ} (t : ℝ) (ht : 0 < t) :
    ∫⁻ x : Vec d, ENNReal.ofReal (gaussianKernel t ht x) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianKernel t ht)
    (Filter.Eventually.of_forall (gaussianKernel_nonneg t ht)), integral_gaussianKernel,
    ENNReal.ofReal_one]

/-- A probability measure satisfies the integral power inequality for every finite `p ≥ 1`.
The extended-real formulation also includes divergent integrals. -/
theorem lintegral_rpow_le_of_probability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f)
    (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ x, f x ∂μ) ^ p ≤ ∫⁻ x, (f x) ^ p ∂μ := by
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le (f := f) (by norm_num : (0 : ℝ) < 1)
    hp μ hf.aestronglyMeasurable
  simp only [eLpNorm'_eq_lintegral_enorm, enorm_eq_self, ENNReal.rpow_one,
    div_one] at h
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow := ENNReal.rpow_le_rpow h hp0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at hpow
  exact hpow

/-- Jensen's integral power inequality with a normalized density. -/
theorem lintegral_rpow_le_of_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w f : α → ℝ≥0∞) (hw : Measurable w) (hf : Measurable f)
    (hw1 : ∫⁻ x, w x ∂μ = 1) (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ x, w x * f x ∂μ) ^ p ≤ ∫⁻ x, w x * (f x) ^ p ∂μ := by
  have : IsProbabilityMeasure (μ.withDensity w) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, hw1]⟩
  have h := lintegral_rpow_le_of_probability (μ.withDensity w) f hf p hp
  rwa [lintegral_withDensity_eq_lintegral_mul μ hw hf,
    lintegral_withDensity_eq_lintegral_mul μ hw (hf.pow_const p)] at h

/-- The Gaussian density can be used in the integral power inequality at every positive time. -/
theorem gaussianKernel_lintegral_rpow_le {d : ℕ} (t : ℝ) (ht : 0 < t)
    (f : Vec d → ℝ≥0∞) (hf : Measurable f) (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ y, ENNReal.ofReal (gaussianKernel t ht y) * f y) ^ p ≤
      ∫⁻ y, ENNReal.ofReal (gaussianKernel t ht y) * (f y) ^ p :=
  lintegral_rpow_le_of_density volume _ f
    (ENNReal.measurable_ofReal.comp (continuous_gaussianKernel t ht).measurable) hf
    (lintegral_gaussianKernel t ht) p hp

/-- Gaussian averaging contracts the integral of the `p`th power. -/
theorem gaussianKernel_lintegral_contraction {d : ℕ} (t : ℝ) (ht : 0 < t)
    (f : Vec d → ℝ≥0∞) (hf : Measurable f) (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, ENNReal.ofReal (gaussianKernel t ht y) * f (x - y)) ^ p) ≤
      ∫⁻ x, (f x) ^ p := by
  have hK : Measurable (fun y : Vec d => ENNReal.ofReal (gaussianKernel t ht y)) :=
    ENNReal.measurable_ofReal.comp (continuous_gaussianKernel t ht).measurable
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (gaussianKernel t ht y) * (f (x - y)) ^ p := by
      apply lintegral_mono
      intro x
      exact gaussianKernel_lintegral_rpow_le t ht _
        (hf.comp (measurable_const.sub measurable_id)) p hp
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (gaussianKernel t ht y) * (f (x - y)) ^ p := by
      apply lintegral_lintegral_swap
      exact ((hK.comp measurable_snd).mul
        ((hf.comp (measurable_fst.sub measurable_snd)).pow_const p)).aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (gaussianKernel t ht y) * (∫⁻ x, (f x) ^ p) := by
      apply lintegral_congr
      intro y
      rw [lintegral_const_mul _ (show Measurable (fun x : Vec d => (f (x - y)) ^ p) from
        (hf.comp (measurable_id.sub measurable_const)).pow_const p),
        lintegral_sub_right_eq_self (fun x => (f x) ^ p) y]
    _ = _ := by
      rw [lintegral_mul_const _ hK, lintegral_gaussianKernel, one_mul]

/-- Young's inequality with unit Gaussian mass for nonnegative extended-real functions. -/
theorem eLpNorm_gaussianKernel_lintegral_le {d : ℕ} (t : ℝ) (ht : 0 < t)
    (f : Vec d → ℝ≥0∞) (hf : Measurable f) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun x => ∫⁻ y, ENNReal.ofReal (gaussianKernel t ht y) * f (x - y))
      (ENNReal.ofReal p) volume ≤ eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hK : Measurable (fun y : Vec d => ENNReal.ofReal (gaussianKernel t ht y)) :=
    ENNReal.measurable_ofReal.comp (continuous_gaussianKernel t ht).measurable
  have hH : Measurable (fun x => ∫⁻ y, ENNReal.ofReal (gaussianKernel t ht y) * f (x - y)) := by
    apply Measurable.lintegral_prod_right' (f := fun z : Vec d × Vec d =>
      ENNReal.ofReal (gaussianKernel t ht z.2) * f (z.1 - z.2))
    exact (hK.comp measurable_snd).mul (hf.comp (measurable_fst.sub measurable_snd))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp0))
      ENNReal.ofReal_ne_top hH.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp0))
      ENNReal.ofReal_ne_top hf.aestronglyMeasurable]
  simp only [enorm_eq_self, ENNReal.toReal_ofReal hp0.le]
  exact ENNReal.rpow_le_rpow (gaussianKernel_lintegral_contraction t ht f hf p hp)
    (one_div_nonneg.mpr hp0.le)

/-- Gaussian convolution is an `Lᵖ` contraction for real normed-space-valued functions.
This includes scalar and matrix fields, with any fixed norm on the target. -/
theorem eLpNorm_gaussianKernel_smul_le {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) (ht : 0 < t)
    (f : Vec d → E) (hf : StronglyMeasurable f) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun x => ∫ y, gaussianKernel t ht y • f (x - y))
      (ENNReal.ofReal p) volume ≤ eLpNorm f (ENNReal.ofReal p) volume := by
  have hK : StronglyMeasurable (gaussianKernel (d := d) t ht) :=
    (continuous_gaussianKernel t ht).stronglyMeasurable
  have hH : AEStronglyMeasurable (fun x => ∫ y, gaussianKernel t ht y • f (x - y)) volume :=
    (((hK.comp_measurable measurable_snd).smul
      (hf.comp_measurable (measurable_fst.sub measurable_snd))).integral_prod_right').aestronglyMeasurable
  calc
    _ ≤ eLpNorm (fun x => ∫⁻ y, ENNReal.ofReal (gaussianKernel t ht y) * ‖f (x - y)‖ₑ)
        (ENNReal.ofReal p) volume := by
      apply eLpNorm_mono_enorm hH
      intro x
      simp only [enorm_eq_self]
      calc
        _ ≤ ∫⁻ y, ‖gaussianKernel t ht y • f (x - y)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
        _ = _ := by
          apply lintegral_congr
          intro y
          rw [enorm_smul, ← ofReal_norm, Real.norm_of_nonneg (gaussianKernel_nonneg t ht y)]
    _ ≤ eLpNorm (fun x => ‖f x‖ₑ) (ENNReal.ofReal p) volume :=
      eLpNorm_gaussianKernel_lintegral_le t ht _ hf.enorm p hp
    _ = _ := eLpNorm_enorm f hf.aestronglyMeasurable

/-- The contraction also holds for a.e. strongly measurable functions, which is
the form needed for zero extensions of integrable coefficient fields. -/
theorem eLpNorm_gaussianKernel_smul_le_ae {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) (ht : 0 < t)
    (f : Vec d → E) (hf : AEStronglyMeasurable f volume) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun x => ∫ y, gaussianKernel t ht y • f (x - y))
      (ENNReal.ofReal p) volume ≤ eLpNorm f (ENNReal.ofReal p) volume := by
  have heq : (fun x => ∫ y, gaussianKernel t ht y • f (x - y)) =
      (fun x => ∫ y, gaussianKernel t ht y • hf.mk f (x - y)) := by
    funext x
    apply integral_congr_ae
    have h := hf.ae_eq_mk.comp_tendsto
      (quasiMeasurePreserving_sub_left_of_right_invariant volume x).tendsto_ae
    filter_upwards [h] with y hy
    simp only [Function.comp_apply] at hy
    rw [hy]
  rw [heq, eLpNorm_congr_ae hf.ae_eq_mk]
  exact eLpNorm_gaussianKernel_smul_le t ht _ hf.stronglyMeasurable_mk p hp

/-- Change of variables between the two conventional convolution orientations. -/
theorem gaussianKernel_integral_smul_swap {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) (ht : 0 < t)
    (f : Vec d → E) (x : Vec d) :
    (∫ y, gaussianKernel t ht (x - y) • f y) =
      ∫ y, gaussianKernel t ht y • f (x - y) := by
  have h := integral_sub_left_eq_self (fun y => gaussianKernel t ht (x - y) • f y) volume x
  simpa only [sub_sub_cancel] using h.symm

/-- The contraction in the exact orientation used by the source heat averages. -/
theorem eLpNorm_gaussianKernel_integral_smul_le {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (t : ℝ) (ht : 0 < t)
    (f : Vec d → E) (hf : AEStronglyMeasurable f volume) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun x => ∫ y, gaussianKernel t ht (x - y) • f y)
      (ENNReal.ofReal p) volume ≤ eLpNorm f (ENNReal.ofReal p) volume := by
  simp_rw [gaussianKernel_integral_smul_swap]
  exact eLpNorm_gaussianKernel_smul_le_ae t ht f hf p hp

end CoarseDeGiorgi.NegSobolev
