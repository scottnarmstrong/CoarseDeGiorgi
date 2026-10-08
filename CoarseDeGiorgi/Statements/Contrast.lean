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
public import CoarseDeGiorgi.Statements.UpperMoment

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def contrast {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s t p q : ℝ)
    (_hs : 0 < s) (_ht : 0 < t) (_hp : 1 ≤ p) (_hq : 1 ≤ q) : ℝ≥0∞ :=
  upperMoment a ha s p _hs _hp / lowerMoment a ha t q _ht _hq

end CoarseDeGiorgi
