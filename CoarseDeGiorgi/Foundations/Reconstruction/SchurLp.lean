module

public import CoarseDeGiorgi.Foundations.Reconstruction.SchurIntegral
public import CoarseDeGiorgi.Foundations.Reconstruction.VectorProjectionLp

/-! # The Euclidean vector-to-scalar Schur bound -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Cauchy–Schwarz uses the Euclidean length, with no dimension loss. -/
theorem norm_vecDot_le_euclidNorm (v w : Vec d) :
    ‖vecDot v w‖ ≤ euclidNorm v * euclidNorm w := by
  have heq : inner ℝ (euclidLinear v) (euclidLinear w) = vecDot v w := by
    simp only [euclidLinear, PiLp.continuousLinearEquiv_symm_apply,
      ContinuousLinearEquiv.coe_coe, EuclideanSpace.inner_toLp_toLp,
      star_trivial, vecDot, dotProduct, mul_comm]
  rw [← heq, ← norm_euclidLinear, ← norm_euclidLinear]
  exact norm_inner_le_norm _ _

/-- Measurability of the finite-coordinate real pairing. -/
theorem measurable_vecDot {X : Type*} [MeasurableSpace X]
    {v w : X → Vec d} (hv : Measurable v) (hw : Measurable w) :
    Measurable (fun x => vecDot (v x) (w x)) := by
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hv).mul ((measurable_pi_apply i).comp hw)

/-- Both kernel integral bounds imply the exact Euclidean-vector Lʳ operator bound. -/
theorem eLpNorm_kernelOperator_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (H : X → Y → Vec d) (g : Y → Vec d)
    (hH : Measurable (Function.uncurry H)) (hg : Measurable g)
    {M : ℝ≥0∞}
    (hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (euclidNorm (H x y)) ∂ν ≤ M)
    (hcol : ∀ y, ∫⁻ x, ENNReal.ofReal (euclidNorm (H x y)) ∂μ ≤ M)
    {r : ℝ} (hr : 1 < r) :
    eLpNorm (fun x => ∫ y, vecDot (H x y) (g y) ∂ν) (ENNReal.ofReal r) μ ≤
      M * eLpNorm (fun y => euclidNorm (g y)) (ENNReal.ofReal r) ν := by
  let T : X → ℝ := fun x => ∫ y, vecDot (H x y) (g y) ∂ν
  let W : X → Y → ℝ≥0∞ := fun x y => ENNReal.ofReal (euclidNorm (H x y))
  let G : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (euclidNorm (g y))
  have hW : Measurable (Function.uncurry W) :=
    (Euclid.continuous_eNorm2.measurable.comp hH).ennreal_ofReal
  have hG : Measurable G :=
    (Euclid.continuous_eNorm2.measurable.comp hg).ennreal_ofReal
  have hT : AEStronglyMeasurable T μ :=
    (measurable_vecDot hH (hg.comp measurable_snd)).stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  have hnorm (x : X) : ‖T x‖ₑ ≤ ∫⁻ y, W x y * G y ∂ν := by
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply lintegral_mono
    intro y
    change ‖vecDot (H x y) (g y)‖ₑ ≤ _
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal (norm_vecDot_le_euclidNorm _ _)).trans_eq
      (ENNReal.ofReal_mul (Euclid.eNorm2_nonneg _))
  have hbound := lintegral_schur_rpow_le μ ν W G hW hG hrow hcol hr
  have hpow : ∫⁻ x, ‖T x‖ₑ ^ r ∂μ ≤ M ^ r * ∫⁻ y, G y ^ r ∂ν :=
    (lintegral_mono fun x => ENNReal.rpow_le_rpow (hnorm x) (by linarith)).trans hbound
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hgm : AEStronglyMeasurable (fun y => euclidNorm (g y)) ν :=
    (Euclid.continuous_eNorm2.measurable.comp hg).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 ENNReal.ofReal_ne_top hT,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 ENNReal.ofReal_ne_top
      hgm,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ r)]
  have h := ENNReal.rpow_le_rpow hpow (by positivity : 0 ≤ 1 / r)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / r),
    ← ENNReal.rpow_mul, show r * (1 / r) = 1 by field_simp,
    ENNReal.rpow_one] at h
  simpa only [G, euclidNorm_eq_eNorm2, ← ofReal_norm, Real.norm_eq_abs,
    abs_of_nonneg (Euclid.eNorm2_nonneg _)] using h

end

end CoarseDeGiorgi.Foundations.Reconstruction
