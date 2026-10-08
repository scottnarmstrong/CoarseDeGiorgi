import CoarseDeGiorgi.Foundations.Reconstruction.FineKernelSmooth

/-! # Physical scaling and uniform higher derivative bounds -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

theorem fineKernelIntegrand_mul (h t : ℝ) (v : Vec d) :
    fineKernelIntegrand (h * t) v =
      (h ^ d)⁻¹ • fineKernelIntegrand t (h⁻¹ • v) := by
  unfold fineKernelIntegrand scaledRho
  simp only [mul_pow, mul_inv_rev, smul_smul]
  rw [show t⁻¹ * h⁻¹ = h⁻¹ * t⁻¹ by ring]
  rw [mul_comm h⁻¹ t⁻¹]
  module

/-- Every positive-scale kernel is a rescaled copy of the unit-scale kernel. -/
theorem fineKernel_scale {h : ℝ} (hh : 0 < h) (v : Vec d) :
    fineKernel h v = (h * (h ^ d)⁻¹) • fineKernel 1 (h⁻¹ • v) := by
  have hI (a b : ℝ) (hab : a ≤ b) (f : ℝ → Vec d) :
      (∫ t in Set.Icc a b, f t ∂volume) = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_of_le hab, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rw [fineKernel, hI h (3 * h) (by linarith)]
  calc
    _ = h • ∫ t in (1 : ℝ)..3, fineKernelIntegrand (h * t) v := by
      simpa only [mul_one, mul_comm h 3] using
        (intervalIntegral.smul_integral_comp_mul_left (fun t => fineKernelIntegrand t v) h
          (a := 1) (b := 3)).symm
    _ = h • ((h ^ d)⁻¹ • ∫ t in (1 : ℝ)..3, fineKernelIntegrand t (h⁻¹ • v)) := by
      simp only [fineKernelIntegrand_mul, intervalIntegral.integral_smul]
    _ = _ := by
      rw [smul_smul, fineKernel, hI 1 (3 * 1) (by norm_num)]
      simp only [mul_one]

theorem hasCompactSupport_fineKernel {h : ℝ} (hh : 0 < h) :
    HasCompactSupport (fineKernel (d := d) h) :=
  (isCompact_closedBall (0 : Vec d) (3 * h / 2)).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (support_fineKernel_subset hh) Metric.isClosed_closedBall)

/-- Compact smooth support gives a common bound for the first three unit-scale jets. -/
theorem exists_bound_unitFineKernel : ∃ A : ℝ, 1 ≤ A ∧
    ∀ i ≤ 2, ∀ x : Vec d, ‖iteratedFDeriv ℝ i (fineKernel 1) x‖ ≤ A := by
  obtain ⟨B, _hB0, hB⟩ := (hasCompactSupport_fineKernel (d := d) (by norm_num : (0 : ℝ) < 1)).exists_bound_iteratedFDeriv (contDiff_fineKernel (by norm_num)) 2
  exact ⟨max 1 B, le_max_left _ _, fun i hi x => (hB i hi x).trans (le_max_right _ _)⟩

/-- At every derivative order, scaling contributes exactly one inverse length per derivative. -/
theorem norm_iteratedFDeriv_fineKernel_le {h A : ℝ} (hh : 0 < h) (hA0 : 0 ≤ A)
    (i : ℕ) (hA : ∀ x : Vec d, ‖iteratedFDeriv ℝ i (fineKernel 1) x‖ ≤ A) (v : Vec d) :
    ‖iteratedFDeriv ℝ i (fineKernel h) v‖ ≤ A * h * (h ^ d)⁻¹ * (h⁻¹) ^ i := by
  let L : Vec d →L[ℝ] Vec d := h⁻¹ • ContinuousLinearMap.id ℝ (Vec d)
  have hL : ‖L‖ ≤ h⁻¹ := by
    dsimp only [L]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hh.le) ContinuousLinearMap.norm_id_le
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fineKernel 1 ∘ L) :=
    (contDiff_fineKernel (by norm_num)).comp L.contDiff
  have heq : fineKernel (d := d) h = fun x => (h * (h ^ d)⁻¹) • (fineKernel 1 ∘ L) x :=
    funext fun x => fineKernel_scale hh x
  rw [heq, iteratedFDeriv_const_smul_apply' (hc.contDiffAt.of_le (by simp)),
    L.iteratedFDeriv_comp_right (contDiff_fineKernel (by norm_num)) v (by simp), norm_smul,
    Real.norm_eq_abs, abs_of_pos (mul_pos hh (inv_pos.mpr (pow_pos hh d)))]
  calc
    _ ≤ (h * (h ^ d)⁻¹) *
        (‖iteratedFDeriv ℝ i (fineKernel 1) (L v)‖ * ∏ _ : Fin i, ‖L‖) :=
      mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
        (by positivity)
    _ ≤ (h * (h ^ d)⁻¹) * (A * (h⁻¹) ^ i) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      gcongr
      exact hA (L v)
    _ = _ := by ring

end

end CoarseDeGiorgi.Foundations.Reconstruction
