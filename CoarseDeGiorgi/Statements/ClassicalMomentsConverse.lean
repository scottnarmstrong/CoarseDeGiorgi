module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Weighted.ResponseBoundsMoments

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem classical_moments_converse :
    ∀ d : ℕ, 3 ≤ d → ∀ p q : ℝ,
      1 < p → 1 < q →
      ∀ s t : ℝ, 0 < s → 0 < t → 0 < paramTheta d p q s t →
        1 / p + 1 / q < 2 / ((d : ℝ) - 1) :=
  CoarseDeGiorgi.Weighted.classical_moments_converse

end CoarseDeGiorgi
