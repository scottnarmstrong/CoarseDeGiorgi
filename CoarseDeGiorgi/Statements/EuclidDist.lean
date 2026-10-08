module

public import Homogenization.Ambient.CoefficientField
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def euclidDist {d : ℕ} (x y : Vec d) : ℝ :=
  Real.sqrt (vecNormSq (x - y))

end

end CoarseDeGiorgi
