import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.PositiveTruncationGradient
import CoarseDeGiorgi.Statements.WeightedEnergy

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def twoLevelQuantity {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (q t : ℝ)
    (ht : 0 < t) (hq : 1 ≤ q)
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (level radius : ℝ) : ℝ≥0∞ :=
  let w := fun x => max (u x - level) 0
  (ENNReal.rpow (eLpNorm w (ENNReal.ofReal (paramR q))
      (volume.restrict (originCube radius))) 2 +
    ENNReal.rpow (lowerMoment a ha t q ht hq) (-1) *
      weightedEnergy a (originCube radius) (positiveTruncationGradient u G level)).rpow (1 / 2)

end CoarseDeGiorgi
