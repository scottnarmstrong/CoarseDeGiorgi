import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.CubeSpatialMomentRange
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

import CoarseDeGiorgi.Cubical.Comparison.Consequences
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
