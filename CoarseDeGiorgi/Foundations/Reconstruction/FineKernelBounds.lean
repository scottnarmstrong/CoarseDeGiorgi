import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicKernelSmooth
import CoarseDeGiorgi.Foundations.Reconstruction.FineDivergence

/-! # Fine kernel jets and periodic divergence -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

variable {d : ℕ}

/-- One dimension-dependent constant bounds the value and first two derivatives at every scale. -/
theorem exists_bound_fineKernel_jets : ∃ A : ℝ, 1 ≤ A ∧ ∀ h : ℝ, 0 < h →
    (∀ v : Vec d, ‖fineKernel h v‖ ≤ A * h * (h ^ d)⁻¹) ∧
    (∀ v : Vec d, ‖fderiv ℝ (fineKernel h) v‖ ≤ A * (h ^ d)⁻¹) ∧
    (∀ v : Vec d, ‖fderiv ℝ (fderiv ℝ (fineKernel h)) v‖ ≤ A * (h ^ d)⁻¹ * h⁻¹) := by
  obtain ⟨A, hA, hbound⟩ := exists_bound_unitFineKernel (d := d)
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA
  refine ⟨A, hA, fun h hh => ⟨?_, ?_, ?_⟩⟩
  · intro v
    have hb := norm_iteratedFDeriv_fineKernel_le hh hA0 0 (hbound 0 (by omega)) v
    simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hb
  · intro v
    have hb := norm_iteratedFDeriv_fineKernel_le hh hA0 1 (hbound 1 (by omega)) v
    rw [norm_iteratedFDeriv_one, pow_one] at hb
    convert hb using 1
    field_simp
  · intro v
    have hb := norm_iteratedFDeriv_fineKernel_le hh hA0 2 (hbound 2 le_rfl) v
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hb
    convert hb using 1
    field_simp

/-- The first derivative vanishes outside the same compact support box. -/
theorem fderiv_fineKernel_eq_zero_of_norm_gt {h : ℝ} (hh : 0 < h) {v : Vec d}
    (hv : 3 * h / 2 < ‖v‖) : fderiv ℝ (fineKernel h) v = 0 := by
  have heq : fineKernel h =ᶠ[𝓝 v] fun _ => (0 : Vec d) := by
    filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hv)] with x hx
    exact fineKernel_eq_zero_of_norm_gt hh hx
  rw [heq.fderiv_eq]
  exact (hasFDerivAt_const (0 : Vec d) v).fderiv

/-- Wrapped scalar mollifier, with no infinite periodization sum. -/
def periodicRho (m : ℤ) (t : ℝ) (v : Vec d) : ℝ := scaledRho t (wrapBox m v)

theorem contDiff_periodicRho {m : ℤ} {t : ℝ} (ht : 0 < t) (hsmall : t ≤ auxSide m) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicRho (d := d) m t) := by
  apply contDiff_comp_wrapBox m (scaledRho t) (contDiff_scaledRho t)
  intro v hv
  exact scaledRho_eq_zero_of_norm_gt ht (lt_of_le_of_lt (by linarith) hv)

theorem periodicRho_add_period (m : ℤ) (t : ℝ) (i : Fin d) (v : Vec d) :
    periodicRho m t (v + (2 * auxSide m) • basisVec i) = periodicRho m t v := by
  unfold periodicRho
  rw [wrapBox_add_period_basisVec]

/-- The periodic fine kernel has the exact difference-of-mollifiers divergence. -/
theorem vectorDivergence_periodicFineKernel {m : ℤ} {h : ℝ} (hh : 0 < h)
    (hsmall : 3 * h ≤ auxSide m) (v : Vec d) :
    vectorDivergence (periodicFineKernel m h) v = periodicRho m h v - periodicRho m (3 * h) v := by
  have hz (x : Vec d) (hx : auxSide m / 2 < ‖x‖) : fineKernel h x = 0 :=
    fineKernel_eq_zero_of_norm_gt hh (lt_of_le_of_lt (by linarith) hx)
  change (∑ i : Fin d, (fderiv ℝ (fun x => fineKernel h (wrapBox m x)) v (basisVec i)) i) = _
  rw [fderiv_comp_wrapBox m (fineKernel h)
    ((contDiff_fineKernel hh).differentiable (by norm_num)) hz]
  exact vectorDivergence_fineKernel hh (wrapBox m v)

/-- The same constant bounds periodic fine kernels, including both derivative orders. -/
theorem exists_bound_periodicFineKernel_jets : ∃ A : ℝ, 1 ≤ A ∧
    ∀ (m : ℤ) (h : ℝ), 0 < h → 3 * h ≤ auxSide m →
      (∀ v : Vec d, ‖periodicFineKernel m h v‖ ≤ A * h * (h ^ d)⁻¹) ∧
      (∀ v : Vec d, ‖fderiv ℝ (periodicFineKernel m h) v‖ ≤ A * (h ^ d)⁻¹) ∧
      (∀ v : Vec d, ‖fderiv ℝ (fderiv ℝ (periodicFineKernel m h)) v‖ ≤
        A * (h ^ d)⁻¹ * h⁻¹) := by
  obtain ⟨A, hA, hbounds⟩ := exists_bound_fineKernel_jets (d := d)
  refine ⟨A, hA, fun m h hh hsmall => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hbounds h hh
  have hz (x : Vec d) (hx : auxSide m / 2 < ‖x‖) : fineKernel h x = 0 :=
    fineKernel_eq_zero_of_norm_gt hh (lt_of_le_of_lt (by linarith) hx)
  have hDz (x : Vec d) (hx : auxSide m / 2 < ‖x‖) : fderiv ℝ (fineKernel h) x = 0 :=
    fderiv_fineKernel_eq_zero_of_norm_gt hh (lt_of_le_of_lt (by linarith) hx)
  have heq : fderiv ℝ (periodicFineKernel (d := d) m h) =
      fun x => fderiv ℝ (fineKernel h) (wrapBox m x) := by
    funext x
    exact fderiv_comp_wrapBox m (fineKernel h)
      ((contDiff_fineKernel hh).differentiable (by norm_num)) hz x
  refine ⟨fun v => h0 (wrapBox m v), ?_, ?_⟩
  · intro v
    rw [heq]
    exact h1 (wrapBox m v)
  · intro v
    rw [heq, fderiv_comp_wrapBox m (fderiv ℝ (fineKernel h))
      (((contDiff_fineKernel hh).fderiv_right (m := 1) (by simp)).differentiable (by norm_num)) hDz]
    exact h2 (wrapBox m v)

end

end CoarseDeGiorgi.Foundations.Reconstruction

