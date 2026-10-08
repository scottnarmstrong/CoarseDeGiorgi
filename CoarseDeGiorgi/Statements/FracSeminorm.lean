import CoarseDeGiorgi.Statements.FracKernel
import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Measure.Prod

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def fracSeminorm {d : ℕ} (V : Set (Vec d)) (α r : ℝ) (w : Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ p : Vec d × Vec d, fracKernel α r w p
    ∂((volume.restrict V).prod (volume.restrict V))).rpow (1 / r)

end

end CoarseDeGiorgi
