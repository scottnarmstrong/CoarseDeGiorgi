import CoarseDeGiorgi.Foundations.Euclid.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Prod

namespace CoarseDeGiorgi.Foundations.Euclid

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The same integrand using Euclidean distance. -/
def euclidKernel (β r : ℝ) (w : Vec d → ℝ) (xy : Vec d × Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (|w xy.1 - w xy.2| ^ r / eDist2 xy.1 xy.2 ^ β)

end

end CoarseDeGiorgi.Foundations.Euclid
