import CoarseDeGiorgi.Foundations.Reconstruction.FineKernel
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiating the fine vector kernels with sup-norm estimates -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

variable {d : ℕ}

theorem fderiv_scaledRho_eq_zero_of_norm_gt {t : ℝ} (ht : 0 < t) {x : Vec d}
    (hx : t / 2 < ‖x‖) : fderiv ℝ (scaledRho t) x = 0 := by
  have hs : tsupport (scaledRho (d := d) t) ⊆ Metric.closedBall 0 (t / 2) :=
    closure_minimal (support_scaledRho_subset ht) Metric.isClosed_closedBall
  by_contra h
  have hx' := hs (support_fderiv_subset ℝ h)
  rw [Metric.mem_closedBall, dist_zero_right] at hx'
  exact (not_le_of_gt hx) hx'

/-- The explicit spatial derivative of the fine-kernel integrand. -/
def fineKernelIntegrandDeriv (t : ℝ) (v : Vec d) : Vec d →L[ℝ] Vec d :=
  (fderiv ℝ (scaledRho t) v).smulRight (t⁻¹ • v) +
    scaledRho t v • (t⁻¹ • ContinuousLinearMap.id ℝ (Vec d))

theorem hasFDerivAt_fineKernelIntegrand (t : ℝ) (v : Vec d) :
    HasFDerivAt (fineKernelIntegrand t) (fineKernelIntegrandDeriv t v) v := by
  have h := ((contDiff_scaledRho t).differentiable (by norm_num) v).hasFDerivAt.smul
    ((hasFDerivAt_id (𝕜 := ℝ) v).const_smul t⁻¹)
  rw [add_comm] at h
  exact h

theorem fineKernelIntegrandDeriv_eq_zero_of_norm_gt {t : ℝ} (ht : 0 < t) {v : Vec d}
    (hv : t / 2 < ‖v‖) : fineKernelIntegrandDeriv t v = 0 := by
  simp only [fineKernelIntegrandDeriv, fderiv_scaledRho_eq_zero_of_norm_gt ht hv,
    scaledRho_eq_zero_of_norm_gt ht hv, ContinuousLinearMap.zero_smulRight, zero_smul,
    add_zero]

/-- The first derivative has one more inverse physical length than the kernel. -/
theorem norm_fineKernelIntegrandDeriv_le {A h t : ℝ} (hh : 0 < h) (ht : h ≤ t)
    (hA0 : 0 ≤ A) (hA : ∀ x : Vec d, ‖reconstructionRho x‖ ≤ A)
    (hDA : ∀ x : Vec d, ‖fderiv ℝ reconstructionRho x‖ ≤ A) (v : Vec d) :
    ‖fineKernelIntegrandDeriv t v‖ ≤ 2 * ((h ^ d)⁻¹ * A * h⁻¹) := by
  have ht0 := hh.trans_le ht
  by_cases hv : t / 2 < ‖v‖
  · rw [fineKernelIntegrandDeriv_eq_zero_of_norm_gt ht0 hv, norm_zero]
    positivity
  · have hv' : ‖v‖ ≤ t / 2 := le_of_not_gt hv
    have hfactor : ‖t⁻¹ • v‖ ≤ (1 / 2 : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
      calc
        t⁻¹ * ‖v‖ ≤ t⁻¹ * (t / 2) := mul_le_mul_of_nonneg_left hv' (inv_nonneg.mpr ht0.le)
        _ = 1 / 2 := by field_simp
    have hid : ‖t⁻¹ • ContinuousLinearMap.id ℝ (Vec d)‖ ≤ t⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
      exact mul_le_of_le_one_right (inv_nonneg.mpr ht0.le) ContinuousLinearMap.norm_id_le
    have hpow : (t ^ d)⁻¹ ≤ (h ^ d)⁻¹ :=
      (inv_le_inv₀ (pow_pos ht0 d) (pow_pos hh d)).mpr (pow_le_pow_left₀ hh.le ht d)
    have hinv : t⁻¹ ≤ h⁻¹ := (inv_le_inv₀ ht0 hh).mpr ht
    calc
      ‖fineKernelIntegrandDeriv t v‖ ≤
          ‖(fderiv ℝ (scaledRho t) v).smulRight (t⁻¹ • v)‖ +
            ‖scaledRho t v • (t⁻¹ • ContinuousLinearMap.id ℝ (Vec d))‖ := norm_add_le _ _
      _ = ‖fderiv ℝ (scaledRho t) v‖ * ‖t⁻¹ • v‖ +
          ‖scaledRho t v‖ * ‖t⁻¹ • ContinuousLinearMap.id ℝ (Vec d)‖ := by
        simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul]
      _ ≤ ((t ^ d)⁻¹ * (A * t⁻¹)) * (1 / 2) + ((t ^ d)⁻¹ * A) * t⁻¹ := by
        exact add_le_add
          (mul_le_mul (norm_fderiv_scaledRho_le ht0 hDA v) hfactor (norm_nonneg _) (by positivity))
          (mul_le_mul (norm_scaledRho_le ht0 hA v) hid (norm_nonneg _) (by positivity))
      _ ≤ 2 * ((t ^ d)⁻¹ * A * t⁻¹) := by
        nlinarith [show 0 ≤ (t ^ d)⁻¹ * A * t⁻¹ by positivity]
      _ ≤ 2 * ((h ^ d)⁻¹ * A * h⁻¹) := by gcongr

theorem continuousOn_fineKernelIntegrandDeriv {h : ℝ} (hh : 0 < h) (v : Vec d) :
    ContinuousOn (fun t => fineKernelIntegrandDeriv t v) (Set.Icc h (3 * h)) := by
  intro t ht
  have ht0 := hh.trans_le ht.1
  have hinv := continuousAt_id.inv₀ ht0.ne'
  have hc : ContinuousAt (fun s : ℝ => (s ^ d)⁻¹) t :=
    (continuousAt_id.pow d).inv₀ (pow_ne_zero _ ht0.ne')
  have hr : ContinuousAt (fun s : ℝ => scaledRho s v) t := by
    exact hc.mul (contDiff_reconstructionRho.continuous.continuousAt.comp
      (hinv.smul continuousAt_const))
  have hD : ContinuousAt (fun s : ℝ => fderiv ℝ (scaledRho s) v) t := by
    simp only [fderiv_scaledRho]
    apply hc.smul
    exact ((contDiff_reconstructionRho (d := d)).continuous_fderiv (by norm_num)).continuousAt.comp
      (hinv.smul continuousAt_const) |>.clm_comp (hinv.smul continuousAt_const)
  exact ((((ContinuousLinearMap.smulRightL ℝ (Vec d) (Vec d)).continuous.continuousAt.comp hD).clm_apply
    (hinv.smul continuousAt_const)).add
    (hr.smul (hinv.smul continuousAt_const))).continuousWithinAt

theorem hasFDerivAt_fineKernel {h : ℝ} (hh : 0 < h) (v : Vec d) :
    HasFDerivAt (fineKernel h)
      (∫ t in Set.Icc h (3 * h), fineKernelIntegrandDeriv t v ∂volume) v := by
  obtain ⟨A, hA, hρ, hDρ⟩ := exists_bound_reconstructionRho (d := d)
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA
  have hm : ∀ x : Vec d, AEStronglyMeasurable (fun t => fineKernelIntegrand t x)
      (volume.restrict (Set.Icc h (3 * h))) :=
    fun x => (integrableOn_fineKernelIntegrand hh x).aestronglyMeasurable
  have hDm : AEStronglyMeasurable (fun t => fineKernelIntegrandDeriv t v)
      (volume.restrict (Set.Icc h (3 * h))) :=
    (continuousOn_fineKernelIntegrandDeriv hh v).integrableOn_Icc.aestronglyMeasurable
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
    (bound := fun _ => 2 * ((h ^ d)⁻¹ * A * h⁻¹)) (by simp)
    (Eventually.of_forall hm) (integrableOn_fineKernelIntegrand hh v) hDm
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht x hx
    exact norm_fineKernelIntegrandDeriv_le hh ht.1 hA0 hρ hDρ x
  · exact integrable_const _
  · exact ae_of_all _ fun t x hx => hasFDerivAt_fineKernelIntegrand t x

theorem fderiv_fineKernel {h : ℝ} (hh : 0 < h) (v : Vec d) :
    fderiv ℝ (fineKernel h) v =
      ∫ t in Set.Icc h (3 * h), fineKernelIntegrandDeriv t v ∂volume :=
  (hasFDerivAt_fineKernel hh v).fderiv

end

end CoarseDeGiorgi.Foundations.Reconstruction
