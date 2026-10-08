import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceLocalization
import Mathlib.Analysis.MeanInequalities

namespace CoarseDeGiorgi.Foundations.FracGeometry
open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section

theorem surfaceNorm_power_eq {d : ℕ} (τ α : ℝ) {r : ℝ} (hr : 0 < r) (F : Vec d → ℝ)
    (hF : Measurable F) :
    surfaceFracNorm τ α r F ^ r = powerIntegral r F (surfaceMeasure τ) +
      ∫⁻ xy, Euclid.euclidKernel ((d : ℝ)-1+α*r) r F xy ∂(surfaceMeasure τ).prod (surfaceMeasure τ) := by
  rw [surfaceFracNorm_rpow τ α hr, eLpNorm_ofReal_rpow hr hF, surfaceFracSeminorm_eq_lintegral,
    ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]; rfl
end
end CoarseDeGiorgi.Foundations.FracGeometry
