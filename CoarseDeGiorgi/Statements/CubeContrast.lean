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
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `Θ̃ = Λ̃_{s,1,p}(□₀) / λ̃_{t,1,q}(□₀)` (`e.cubical.simplicial.ratio`). -/
noncomputable def cubeContrast {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s t p q : ℝ)
    (_hs : 0 < s) (_ht : 0 < t) (_hp : 1 ≤ p) (_hq : 1 ≤ q) : ℝ≥0∞ :=
  cubeUpperMoment a ha s p _hs _hp / cubeLowerMoment a ha t q _ht _hq

end CoarseDeGiorgi
