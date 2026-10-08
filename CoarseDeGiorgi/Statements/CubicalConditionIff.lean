module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.CubeSpatialMomentRange
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube

public import CoarseDeGiorgi.Cubical.Comparison.Consequences

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Under `e.cubical.simplicial.range`, `e.spatial.moment.range` is equivalent to the condition with `Λ̃, λ̃`
(the paragraph after it). -/
theorem cubical_condition_iff (d : ℕ) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q))
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) :
    spatialMomentRange a ha p q s t ↔ cubeSpatialMomentRange a ha p q s t
:=
  by exact CoarseDeGiorgi.Cubical.cubical_condition_iff_of_equivalence d p q s t hp hq hs ht _hsp _htq a ha

end CoarseDeGiorgi
