module

public import CoarseDeGiorgi.SharpnessExamples.ScalarMeans
public import CoarseDeGiorgi.SharpnessExamples.CylinderAveragesDiscounted
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integration and cell averages of absolutely summable scalar series -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

/-- An absolutely summable series in integral norm is integrable. -/
theorem integrable_tsum_of_summable_integral_norm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} (hf : ∀ j, Integrable (f j) μ)
    (hs : Summable (fun j => ∫ x, ‖f j x‖ ∂μ)) :
    Integrable (fun x => ∑' j, f j x) μ := by
  refine ⟨AEStronglyMeasurable.tsum (fun j => (hf j).aestronglyMeasurable), ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  calc
    ∫⁻ x, ‖∑' j, f j x‖ₑ ∂μ ≤ ∫⁻ x, ∑' j, ‖f j x‖ₑ ∂μ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' j, ∫⁻ x, ‖f j x‖ₑ ∂μ :=
      lintegral_tsum (fun j => (hf j).aestronglyMeasurable.enorm)
    _ = ∑' j, ENNReal.ofReal (∫ x, ‖f j x‖ ∂μ) := by
      congr 1
      funext j
      exact (ofReal_integral_norm_eq_lintegral_enorm (hf j)).symm
    _ < ⊤ := hs.tsum_ofReal_lt_top

/-- A normalized cell average commutes with an absolutely summable series. -/
theorem volumeAverage_tsum_of_summable_integral_norm {d : ℕ}
    (V : Set (Vec d)) (f : ℕ → Vec d → ℝ)
    (hf : ∀ j, IntegrableOn (f j) V volume)
    (hs : Summable (fun j => ∫ x in V, ‖f j x‖ ∂volume)) :
    volumeAverage V (fun x => ∑' j, f j x) = ∑' j, volumeAverage V (f j) := by
  unfold volumeAverage
  rw [← integral_tsum_of_summable_integral_norm hf hs, tsum_mul_left]

/-- Averaging a scalar identity field amounts to averaging its scalar. -/
theorem volumeAverageMat_scalar_identity {d : ℕ} (V : Set (Vec d))
    (f : Vec d → ℝ) :
    volumeAverageMat V (fun x => f x • (1 : Mat d)) = volumeAverage V f • (1 : Mat d) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [volumeAverageMat, Matrix.smul_apply, volumeAverage]
  · simp [volumeAverageMat, Matrix.smul_apply, Matrix.one_apply_ne hij, volumeAverage]

/-- The operator norm of a nonnegative scalar average is the average itself. -/
theorem norm_volumeAverageMat_scalar_identity {d : ℕ} [NeZero d]
    (V : Set (Vec d)) (f : Vec d → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ‖volumeAverageMat V (fun x => f x • (1 : Mat d))‖ = volumeAverage V f := by
  rw [volumeAverageMat_scalar_identity, norm_smul, norm_one, Real.norm_eq_abs]
  have hmean : 0 ≤ volumeAverage V f := by
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hf)
  rw [abs_of_nonneg hmean, mul_one]

end CoarseDeGiorgi.SharpnessExamples
