import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.CubeUpperMoment
import CoarseDeGiorgi.Statements.CubeLowerMoment
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

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
