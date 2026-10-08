import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.Triangulation

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def lowerCellAverage {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (q : ℝ) : ℝ := by
  classical
  exact
    ((triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q) /
        ((triangulation (d := d) k).card : ℝ)

end CoarseDeGiorgi
