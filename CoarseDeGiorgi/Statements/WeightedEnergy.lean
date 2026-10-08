module

public import Homogenization.Ambient.CoefficientField

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def weightedEnergy {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) : ENNReal :=
  ∫⁻ x in U,
    ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))

end CoarseDeGiorgi
