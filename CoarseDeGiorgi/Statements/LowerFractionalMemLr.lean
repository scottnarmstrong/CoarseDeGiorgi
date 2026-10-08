import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.SpatialMomentRange

import CoarseDeGiorgi.LowerFractional.CubeFinal
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.lower.fractional`, last sentence: every `w ∈ H¹_a(□₀)` belongs to `L^r(□₀)`. -/
theorem lower_fractional_memLr {d : ℕ} (hd : 3 ≤ d) (p q s t : ℝ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t)
    (w : Vec d → ℝ) (G : Vec d → Vec d) (hw : MemH1a a (originCube 1) w G) :
    MemLp w (ENNReal.ofReal (paramR q)) (volume.restrict (originCube 1))
:=
  LowerFractional.lower_fractional_memLr_proved hd p q s t a ha hrange w G hw

end CoarseDeGiorgi
