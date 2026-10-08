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
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.Triangulation
public import CoarseDeGiorgi.Statements.UpperResponseOnCell

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def upperCellAverage {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (p : ℝ) : ℝ := by
  classical
  exact
    ((triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖upperResponseOnCell k a ha η‖ p) /
        ((triangulation (d := d) k).card : ℝ)

end CoarseDeGiorgi
