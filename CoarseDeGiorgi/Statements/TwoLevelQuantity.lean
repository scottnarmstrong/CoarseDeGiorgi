module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.PositiveTruncationGradient
public import CoarseDeGiorgi.Statements.WeightedEnergy

@[expose] public section

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
