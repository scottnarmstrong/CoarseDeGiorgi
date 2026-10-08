import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Weighted.ResponseBoundsMoments

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
