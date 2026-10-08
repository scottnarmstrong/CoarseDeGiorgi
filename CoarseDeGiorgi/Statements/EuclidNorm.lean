module

public import Homogenization.Ambient.CoefficientField
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def euclidNorm {d : ℕ} (v : Vec d) : ℝ :=
  Real.sqrt (vecNormSq v)

end

end CoarseDeGiorgi
