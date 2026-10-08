module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.CubeUpperMoment
public import CoarseDeGiorgi.Statements.CubeLowerMoment
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The condition `e.spatial.moment.range` with `Λ, λ` replaced by `Λ̃, λ̃` (the paragraph after it); compare `spatialMomentRange`. -/
noncomputable def cubeSpatialMomentRange {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (p q s t : ℝ) : Prop :=
  ∃ (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 0 < s) (ht : 0 < t),
    1 < p ∧ 1 < q ∧ 0 < s ∧ 0 < t ∧ 0 < paramTheta d p q s t ∧
      cubeUpperMoment a ha s p hs hp < ⊤ ∧ 0 < cubeLowerMoment a ha t q ht hq

end CoarseDeGiorgi
