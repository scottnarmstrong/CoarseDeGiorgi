import CoarseDeGiorgi.SharpnessExamples.CylinderResponseDefs
import CoarseDeGiorgi.Weighted.UpperSpecHarmonic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Axial harmonicity of a cylindrical coefficient

The discontinuity across the cylinder causes no axial divergence: the axial
conductivity is constant along every line parallel to the first coordinate.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Classical

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Adding an axial vector does not change the transverse distance. -/
theorem transverseNorm_add_axial {d : ℕ} [NeZero d] (x : Vec d) (t : ℝ) :
    Sharpness.transverseNorm (x + t • basisVec (0 : Fin d)) =
      Sharpness.transverseNorm x := by
  apply congrArg euclideanNorm
  funext i
  by_cases hi : i.val = 0
  · simp [Sharpness.transversePart, hi]
  · have hi0 : i ≠ (0 : Fin d) := fun h => hi (congrArg Fin.val h)
    simp [Sharpness.transversePart, hi, basisVec, hi0]

/-- A bounded measurable axial conductivity pairs to zero with the axial
partial derivative of every compactly supported smooth test. -/
theorem integral_axial_test_eq_zero {d : ℕ} [NeZero d]
    {b : Vec d → ℝ} (hb : Measurable b) {M : ℝ}
    (hbnd : ∀ x, ‖b x‖ ≤ M)
    (hinv : ∀ (x : Vec d) (t : ℝ), b (x + t • basisVec (0 : Fin d)) = b x)
    {phi : Vec d → ℝ} (hphi : ContDiff ℝ (⊤ : ℕ∞) phi)
    (hc : HasCompactSupport phi) :
    ∫ x, b x * smoothGrad phi x 0 = 0 := by
  have hdiff : ∀ x, DifferentiableAt ℝ phi x :=
    fun x => (hphi.differentiable (by simp)).differentiableAt
  have hdc : Continuous (fun x => fderiv ℝ phi x (basisVec (0 : Fin d))) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdint := hdc.integrable_of_hasCompactSupport (μ := volume)
    (hc.fderiv_apply (𝕜 := ℝ) (basisVec (0 : Fin d)))
  have hleft := hdint.bdd_mul hb.aestronglyMeasurable (ae_of_all _ hbnd)
  have hprod := (hphi.continuous.integrable_of_hasCompactSupport (μ := volume) hc).bdd_mul
    hb.aestronglyMeasurable (ae_of_all _ hbnd)
  have hline (x : Vec d) : HasLineDerivAt ℝ b 0 x (basisVec (0 : Fin d)) := by
    unfold HasLineDerivAt
    have heq : (fun t : ℝ => b (x + t • basisVec (0 : Fin d))) = fun _ => b x :=
      funext (hinv x)
    rw [heq]
    exact hasDerivAt_const _ _
  have hparts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := b) (f' := fun _ => 0) (g := phi)
    (g' := fun x => fderiv ℝ phi x (basisVec (0 : Fin d)))
    (by simp) hleft hprod (fun x _ => hline x)
    (fun x _ => (hdiff x).hasFDerivAt.hasLineDerivAt _)
  simpa only [smoothGrad, CoarseDeGiorgi.smoothGrad, ContinuousLinearMap.mul_apply', zero_mul, integral_zero, neg_zero] using hparts

end

end CoarseDeGiorgi.SharpnessExamples
