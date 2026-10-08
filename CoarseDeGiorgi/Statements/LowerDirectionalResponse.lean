module

public import CoarseDeGiorgi.Statements.IsWeightedSolution
public import Homogenization.Ambient.CoefficientField
public import Homogenization.CoarseGraining.Definitions
public import Mathlib.Data.EReal.Basic

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def lowerDirectionalResponse {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) : EReal :=
  ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
    (_ : IsWeightedSolution a V w G),
    ((volumeAverage V
      (fun x =>
        -vecDot (G x) (matVecMul (a x) (G x)) +
          2 * vecDot e (G x)) : ℝ) : EReal)

end CoarseDeGiorgi
