import Homogenization.Ambient.CoefficientField

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def infSupDist {d : ℕ} (A B : Set (Vec d)) : ℝ :=
  sInf ((fun p : Vec d × Vec d => dist p.1 p.2) '' (A ×ˢ B))

end

end CoarseDeGiorgi
