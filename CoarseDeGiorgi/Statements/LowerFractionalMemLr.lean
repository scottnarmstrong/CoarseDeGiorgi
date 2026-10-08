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
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.SpatialMomentRange

public import CoarseDeGiorgi.LowerFractional.CubeFinal

@[expose] public section

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
