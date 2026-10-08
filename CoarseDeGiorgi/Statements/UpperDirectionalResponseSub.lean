import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import Homogenization.Ambient.CoefficientField
import Homogenization.CoarseGraining.Definitions
import Mathlib.Data.EReal.Basic

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def upperDirectionalResponseSub {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) : EReal :=
  ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
    (_ : IsWeightedSubsolution a V w G),
    ((volumeAverage V
      (fun x =>
        -vecDot (G x) (matVecMul (a x) (G x)) +
          2 * vecDot e (matVecMul (a x) (G x))) : ℝ) : EReal)

end CoarseDeGiorgi
