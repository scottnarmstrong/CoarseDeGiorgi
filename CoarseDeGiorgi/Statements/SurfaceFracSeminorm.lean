import CoarseDeGiorgi.Statements.FracKernelWithDimension
import CoarseDeGiorgi.Statements.SurfaceMeasure
import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Measure.Prod

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def surfaceFracSeminorm {d : ℕ} (τ α r : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ p : Vec d × Vec d, fracKernelWithDimension ((d : ℝ) - 1) α r f p
    ∂((surfaceMeasure τ).prod (surfaceMeasure τ))).rpow (1 / r)

end

end CoarseDeGiorgi
