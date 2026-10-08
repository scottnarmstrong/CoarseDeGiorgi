module

public import CoarseDeGiorgi.Foundations.Euclid.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

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
