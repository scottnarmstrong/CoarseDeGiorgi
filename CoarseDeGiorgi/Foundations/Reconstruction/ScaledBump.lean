import CoarseDeGiorgi.Foundations.Reconstruction.ProductBump
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Scaled probability bumps and their sup-norm bounds -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

/-- One-dimensional scaled probability bump. -/
def scaledEta (t x : ℝ) : ℝ := t⁻¹ * reconstructionEta (t⁻¹ * x)

/-- Sup-norm product mollifier at physical length `t`. -/
def scaledRho {d : ℕ} (t : ℝ) (x : Vec d) : ℝ :=
  (t ^ d)⁻¹ * reconstructionRho (t⁻¹ • x)

variable {d : ℕ}

theorem scaledRho_eq_prod (t : ℝ) (x : Vec d) :
    scaledRho t x = ∏ i : Fin d, scaledEta t (x i) := by
  simp only [scaledRho, reconstructionRho, scaledEta, Pi.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]

theorem contDiff_scaledRho (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scaledRho (d := d) t) :=
  contDiff_const.mul (contDiff_reconstructionRho.comp (contDiff_id.const_smul t⁻¹))

theorem integrable_scaledEta {t : ℝ} (ht : 0 < t) : Integrable (scaledEta t) volume := by
  change Integrable (fun x => t⁻¹ * reconstructionEta (t⁻¹ * x)) volume
  simpa only [smul_eq_mul] using
    (integrable_reconstructionEta.comp_smul (inv_ne_zero ht.ne')).const_mul t⁻¹

theorem integral_scaledEta {t : ℝ} (ht : 0 < t) : ∫ x, scaledEta t x ∂volume = 1 := by
  unfold scaledEta
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul (volume : Measure ℝ) reconstructionEta t⁻¹
  simp only [Module.finrank_self, pow_one, inv_inv, abs_of_pos ht, smul_eq_mul,
    integral_reconstructionEta, mul_one] at h
  change (∫ x, reconstructionEta (t⁻¹ * x) ∂volume) = t at h
  rw [h, inv_mul_cancel₀ ht.ne']

theorem integrable_scaledRho {t : ℝ} (ht : 0 < t) :
    Integrable (scaledRho (d := d) t) volume := by
  rw [funext (scaledRho_eq_prod t)]
  exact Integrable.fintype_prod fun _ : Fin d => integrable_scaledEta ht

theorem integral_scaledRho {t : ℝ} (ht : 0 < t) :
    ∫ x : Vec d, scaledRho t x ∂volume = 1 := by
  simp only [funext (scaledRho_eq_prod t)]
  rw [integral_fintype_prod_volume_eq_pow, integral_scaledEta ht, one_pow]

theorem support_scaledRho_subset {t : ℝ} (ht : 0 < t) :
    Function.support (scaledRho (d := d) t) ⊆ Metric.closedBall 0 (t / 2) := by
  intro x hx
  have hr : reconstructionRho (t⁻¹ • x) ≠ 0 := (mul_ne_zero_iff.mp hx).2
  have hnorm := support_reconstructionRho_subset hr
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ht)] at hnorm
  rw [Metric.mem_closedBall, dist_zero_right]
  have hmul := mul_le_mul_of_nonneg_left hnorm ht.le
  rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at hmul
  linarith

theorem scaledRho_eq_zero_of_norm_gt {t : ℝ} (ht : 0 < t) {x : Vec d}
    (hx : t / 2 < ‖x‖) : scaledRho t x = 0 := by
  by_contra h
  have hs := support_scaledRho_subset ht h
  rw [Metric.mem_closedBall, dist_zero_right] at hs
  exact (not_le_of_gt hx) hs

/-- Scaling gains one inverse physical length in the spatial derivative. -/
theorem fderiv_scaledRho (t : ℝ) (x : Vec d) :
    fderiv ℝ (scaledRho t) x = (t ^ d)⁻¹ •
      (fderiv ℝ reconstructionRho (t⁻¹ • x)).comp
        (t⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) := by
  have hr := (contDiff_reconstructionRho (d := d)).differentiable (by norm_num)
  have hi := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul t⁻¹
  exact (((hr (t⁻¹ • x)).hasFDerivAt.comp x hi).const_smul (t ^ d)⁻¹).fderiv

theorem norm_scaledRho_le {A t : ℝ} (ht : 0 < t)
    (hA : ∀ x : Vec d, ‖reconstructionRho x‖ ≤ A) (x : Vec d) :
    ‖scaledRho t x‖ ≤ (t ^ d)⁻¹ * A := by
  rw [scaledRho, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos ht _))]
  exact mul_le_mul_of_nonneg_left (hA _) (inv_nonneg.mpr (pow_nonneg ht.le _))

theorem norm_fderiv_scaledRho_le {A t : ℝ} (ht : 0 < t)
    (hA : ∀ x : Vec d, ‖fderiv ℝ reconstructionRho x‖ ≤ A) (x : Vec d) :
    ‖fderiv ℝ (scaledRho t) x‖ ≤ (t ^ d)⁻¹ * (A * t⁻¹) := by
  rw [fderiv_scaledRho, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos ht _))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg ht.le _))
  calc
    ‖(fderiv ℝ reconstructionRho (t⁻¹ • x)).comp
        (t⁻¹ • ContinuousLinearMap.id ℝ (Vec d))‖
      ≤ ‖fderiv ℝ reconstructionRho (t⁻¹ • x)‖ *
          ‖t⁻¹ • ContinuousLinearMap.id ℝ (Vec d)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ A * t⁻¹ := by
      apply mul_le_mul (hA _) _ (norm_nonneg _)
        ((norm_nonneg (fderiv ℝ reconstructionRho (0 : Vec d))).trans (hA 0))
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      exact mul_le_of_le_one_right (inv_nonneg.mpr ht.le) ContinuousLinearMap.norm_id_le

end

end CoarseDeGiorgi.Foundations.Reconstruction
