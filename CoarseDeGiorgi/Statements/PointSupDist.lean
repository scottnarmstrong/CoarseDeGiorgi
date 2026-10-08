import Homogenization.Ambient.CoefficientField

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def pointSupDist {d : ℕ} (x : Vec d) (S : Set (Vec d)) : ℝ :=
  sInf (dist x '' S)

end

end CoarseDeGiorgi
