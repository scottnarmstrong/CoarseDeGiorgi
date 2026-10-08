import Homogenization.Besov.Duality.ProjectionLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Strong L¹ convergence of the triadic averaging operators

A.e. convergence and the L¹ contraction suffice: the reverse-triangle
defect is dominated by twice the norm of the limiting function.
-/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped Topology

noncomputable section

/-- A.e. convergence of L¹ contractions toward their input is strong L¹
convergence. The proof uses a fixed dominator, not uniform integrability. -/
theorem tendsto_integral_norm_sub_of_ae_of_integral_norm_le
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {f : X → E} {g : ℕ → X → E}
    (hf : Integrable f μ) (hg : ∀ n, Integrable (g n) μ)
    (hcontract : ∀ n, ∫ x, ‖g n x‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, ‖g n x - f x‖ ∂μ) atTop (𝓝 0) := by
  let defect : ℕ → X → ℝ := fun n x => ‖g n x‖ + ‖f x‖ - ‖g n x - f x‖
  have hdefect_nonneg : ∀ n x, 0 ≤ defect n x := by
    intro n x
    exact sub_nonneg.mpr (norm_sub_le _ _)
  have hdefect_bound : ∀ n x, defect n x ≤ 2 * ‖f x‖ := by
    intro n x
    have h := norm_le_norm_sub_add (g n x) (f x)
    dsimp only [defect]
    linarith
  have hdefect_lim : Tendsto (fun n => ∫ x, defect n x ∂μ) atTop
      (𝓝 (2 * ∫ x, ‖f x‖ ∂μ)) := by
    have h : Tendsto (fun n => ∫ x, defect n x ∂μ) atTop
        (𝓝 (∫ x, 2 * ‖f x‖ ∂μ)) :=
      tendsto_integral_of_dominated_convergence (fun x => 2 * ‖f x‖)
      (fun n => ((hg n).norm.add hf.norm).aestronglyMeasurable.sub
        ((hg n).sub hf).norm.aestronglyMeasurable)
      (hf.norm.const_mul 2)
      (fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hdefect_nonneg n x)]
        exact hdefect_bound n x)
      (hlim.mono fun x hx => by
        simpa [defect, two_mul] using
          (hx.norm.add (tendsto_const_nhds (x := ‖f x‖))).sub
            (hx.sub (tendsto_const_nhds (x := f x))).norm)
    simpa only [integral_const_mul] using h
  have hupper : ∀ n, ∫ x, ‖g n x - f x‖ ∂μ ≤
      2 * ∫ x, ‖f x‖ ∂μ - ∫ x, defect n x ∂μ := by
    intro n
    have hid : ∫ x, defect n x ∂μ =
        (∫ x, ‖g n x‖ ∂μ) + (∫ x, ‖f x‖ ∂μ) -
          ∫ x, ‖g n x - f x‖ ∂μ := by
      exact (integral_sub ((hg n).norm.add hf.norm) ((hg n).sub hf).norm).trans
        (by
          dsimp only [Pi.add_apply, Pi.sub_apply]
          rw [integral_add (hg n).norm hf.norm])
    linarith [hcontract n]
  apply squeeze_zero (fun n => integral_nonneg fun _ => norm_nonneg _) hupper
  simpa using (tendsto_const_nhds (x := 2 * ∫ x, ‖f x‖ ∂μ)).sub hdefect_lim

variable {d : ℕ}

/-- The ordinary-volume L¹ contraction of the scalar triadic projection. -/
theorem integral_norm_cubeProjection_le (Q : TriadicCube d) (n : ℕ)
    (f : Vec d → ℝ) (hf : IntegrableOn f (cubeSet Q) volume) :
    ∫ x in cubeSet Q, ‖cubeProjection Q n f x‖ ∂volume ≤
      ∫ x in cubeSet Q, ‖f x‖ ∂volume := by
  have hfμ : Integrable f (normalizedCubeMeasure Q) :=
    hf.smul_measure ENNReal.ofReal_ne_top
  have hgμ : Integrable (cubeProjection Q n f) (normalizedCubeMeasure Q) :=
    (integrableOn_cubeProjection_of_integrableOn Q n f).smul_measure ENNReal.ofReal_ne_top
  have h := cubeLpNorm_cubeProjection_le Q 1 f n le_rfl (by simp)
    (memLp_one_iff_integrable.mpr hfμ)
  rw [cubeLpNorm_one_eq_integral_norm Q _ hgμ.aestronglyMeasurable,
    cubeLpNorm_one_eq_integral_norm Q _ hfμ.aestronglyMeasurable,
    ← cubeAverage_eq_integral_normalizedCubeMeasure,
    ← cubeAverage_eq_integral_normalizedCubeMeasure] at h
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr (cubeVolume_pos Q))).mp h

/-- Strong L¹ convergence of cube averages requires only L¹ input. -/
theorem tendsto_integral_norm_cubeProjection_sub (Q : TriadicCube d)
    (f : Vec d → ℝ) (hf : IntegrableOn f (cubeSet Q) volume) :
    Tendsto (fun n => ∫ x in cubeSet Q, ‖cubeProjection Q n f x - f x‖ ∂volume)
      atTop (𝓝 0) :=
  tendsto_integral_norm_sub_of_ae_of_integral_norm_le hf
    (fun n => integrableOn_cubeProjection_of_integrableOn Q n f)
    (fun n => integral_norm_cubeProjection_le Q n f hf)
    (ae_tendsto_cubeProjection_of_integrableOn Q f hf)

end

end CoarseDeGiorgi.Foundations.Reconstruction
