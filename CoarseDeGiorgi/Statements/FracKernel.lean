import CoarseDeGiorgi.Statements.FracKernelWithDimension
import Homogenization.Ambient.CoefficientField

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def fracKernel {d : ℕ} (α r : ℝ) (w : Vec d → ℝ)
    (p : Vec d × Vec d) : ℝ≥0∞ :=
  fracKernelWithDimension (d : ℝ) α r w p

end

end CoarseDeGiorgi
