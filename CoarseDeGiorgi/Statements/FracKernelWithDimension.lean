import CoarseDeGiorgi.Statements.EuclidDist
import Homogenization.Ambient.CoefficientField
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def fracKernelWithDimension {d : ℕ} (dimension α r : ℝ) (w : Vec d → ℝ)
    (p : Vec d × Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal
    (|w p.1 - w p.2| ^ r /
      euclidDist p.1 p.2 ^ (dimension + α * r))

end

end CoarseDeGiorgi
